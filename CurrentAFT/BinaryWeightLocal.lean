import CurrentAFT.BinaryPairedTensor
import CurrentAFT.BinaryWeightCoordinates
import CurrentAFT.RationalWeightProgram

/-! # Joint-table readers and the actual cached primary tensor -/
namespace CurrentAFT.BinaryWeightLocal
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

theorem colors_pos (security : ℕ) : 0 < colors security := by
  change 0 < (PublicParameterProgram.modulus security).count
  rw [PublicParameterProgram.modulus_value]
  exact (Parameters.modulus_spec security).2.pos

def gather {Value : Type*} {pool count : ℕ} (fallback : Value) (hp : 0 < pool)
    (values : Vector Value pool) (sites : Vector (Fin pool) count) : CountedValue (Vector Value count) :=
  let computed := Vector.ofFn (fun slot : Fin count =>
    let index := readVector ⟨0, hp⟩ sites slot
    let value := readVector fallback values index.value
    (⟨value.value, index.work+value.work+2⟩ : CountedValue Value))
  ⟨computed.map (fun result => result.value), (∑ slot, (computed.get slot).work)+2*count+2⟩

theorem gather_get {Value : Type*} {pool count : ℕ} (fallback : Value) (hp : 0 < pool)
    (values : Vector Value pool) (sites : Vector (Fin pool) count) (slot : Fin count) :
    (gather fallback hp values sites).value.get slot = values.get (sites.get slot) := by
  simp [gather, readVector_value]

def gatherWork (pool count : ℕ) : ℕ := count*(3*count+3*pool+10)+2

theorem gather_work {Value : Type*} {pool count : ℕ} (fallback : Value) (hp : 0 < pool)
    (values : Vector Value pool) (sites : Vector (Fin pool) count) :
    (gather fallback hp values sites).work ≤ gatherWork pool count := by
  have hw (slot : Fin count) :
      (readVector (⟨0, hp⟩ : Fin pool) sites slot).work+
        (readVector fallback values (readVector (⟨0, hp⟩ : Fin pool) sites slot).value).work+2 ≤ 3*count+3*pool+8 := by
    have hs := readVector_work (⟨0, hp⟩ : Fin pool) sites slot
    have hv := readVector_work fallback values (readVector (⟨0, hp⟩ : Fin pool) sites slot).value
    omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun slot _ => hw slot)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  simp only [gather, Vector.get_ofFn, gatherWork]
  nlinarith

def rawTable (security order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order) : RationalWeightProgram.RawTable order :=
  fun arity primary body =>
    if h : (∀ index, primary index < colors security) ∧ (∀ index, body index < colors security) then
      ((table.get (WeightCoordinates.arityIndex order arity.val.1 arity.val.2)).get
        ⟨WeightCoordinates.jointCode (colors security) arity.val.1.val arity.val.2.val primary body,
          WeightCoordinates.jointCode_lt_capacity _ _ _ _
            (colors_pos security)
            arity.property primary body h.1 h.2⟩).decode
    else 0

theorem rawTable_value (security order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (arity : TruncatedArity order) (primary : Fin arity.val.1.val → Fin (colors security))
    (body : Fin arity.val.2.val → Fin (colors security)) :
    rawTable security order table arity (fun index => (primary index).val) (fun index => (body index).val) =
      ((table.get (WeightCoordinates.arityIndex order arity.val.1 arity.val.2)).get
        (WeightCoordinates.wordIndex (colors security) order arity.val.1.val arity.val.2.val
          (colors_pos security)
          arity.property primary body)).decode := by
  unfold rawTable
  rw [dif_pos ⟨fun index => (primary index).isLt, fun index => (body index).isLt⟩]
  rfl

private theorem cons_val {count colors : ℕ} (color : Fin colors) (rest : Fin count → Fin colors) :
    (fun index : Fin (count+1) => (Fin.cons (α := fun _ => Fin colors) color rest index).val) =
      Fin.cons color.val (fun index => (rest index).val) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem tensor_value (security bits count : ℕ) (kernel : (Fin count → Fin (colors security)) → ℚ)
    (ideal : (Fin count → ℕ) → ℚ)
    (hk : ∀ word, kernel word = ideal (fun index => (word index).val))
    (groups : Fin count → Fin (colors security) × Fin (colors security)) :
    BinaryPairedTensor.value (BinaryReferenceTables.current security bits).primary (BinaryReferenceTables.current security bits).center
      (BinaryReferenceTables.current security bits).anchor (BinaryReferenceTables.current security bits).activation count kernel groups =
      RationalWeightProgram.pairedTensor security bits count ideal
        (fun index => ((groups index).1.val, (groups index).2.val)) := by
  induction count with
  | zero =>
    simp only [BinaryPairedTensor.value, RationalWeightProgram.pairedTensor]
    exact (hk Fin.elim0).trans (congrArg ideal (Subsingleton.elim _ _))
  | succ count ih =>
    simp only [BinaryPairedTensor.value, BinaryPairedTensor.lift, RationalWeightProgram.pairedTensor,
      RationalPairedLiftProgram.current, RationalPairedLiftProgram.anchorProfile]
    simp_rw [BinaryReferenceTables.primary_value, BinaryReferenceTables.anchor_value]
    rw [BinaryReferenceTables.center_value, BinaryReferenceTables.activation_value]
    have hchild (color : Fin (colors security)) := ih
      (fun rest => kernel (Fin.cons color rest)) (fun rest => ideal (Fin.cons color.val rest))
      (fun rest => (hk (Fin.cons color rest)).trans (congrArg ideal (cons_val color rest)))
      (fun index => groups index.succ)
    simp_rw [hchild]

def current (security _bits order : ℕ) (references : BinaryReferenceTables.Result security)
    (table : BinaryWeightCoordinates.Table (colors security) order) (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) arity.val.1.val)
    (centers : Vector (Fin (colors security)) arity.val.2.val) : RationalResult :=
  BinaryPairedTensor.current references.primary references.center references.anchor references.activation
    (⟨0, colors_pos security⟩,
     ⟨0, colors_pos security⟩)
    arity.val.1.val (fun primary => BinaryWeightCoordinates.read (colors security) order arity.val.1.val arity.val.2.val
      (colors_pos security)
      arity.property table primary centers) groups

theorem current_value (security bits order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) arity.val.1.val)
    (centers : Vector (Fin (colors security)) arity.val.2.val) :
    (current security bits order (BinaryReferenceTables.current security bits) table arity groups centers).data.decode =
      RationalWeightProgram.pairedTensor security bits arity.val.1.val
        (fun primary => rawTable security order table arity primary (fun index => (centers.get index).val))
        (fun index => ((groups.get index).1.val, (groups.get index).2.val)) := by
  rw [current, BinaryPairedTensor.current_value]
  apply tensor_value
  intro primary
  rw [BinaryWeightCoordinates.read_value, rawTable_value]
  simp only [BinaryTupleSum.get_ofFn_fun]

theorem current_bounds (security bits order : ℕ) (references : BinaryReferenceTables.Result security)
    (table : BinaryWeightCoordinates.Table (colors security) order) (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) arity.val.1.val)
    (centers : Vector (Fin (colors security)) arity.val.2.val) (referenceHeight tableHeight : ℕ)
    (hp : ∀ color, HeightBound (references.primary.get color).decode referenceHeight)
    (hb : ∀ color, HeightBound (references.center.get color).decode referenceHeight)
    (ha : ∀ input output, HeightBound ((references.anchor.get input).get output).decode referenceHeight)
    (hr : HeightBound references.activation.decode referenceHeight)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode tableHeight) :
    HeightBound (current security bits order references table arity groups centers).data.decode
      (BinaryPairedTensor.height (colors security) referenceHeight arity.val.1.val tableHeight) ∧
    (current security bits order references table arity groups centers).work ≤
      BinaryPairedTensor.work (colors security) referenceHeight arity.val.1.val tableHeight
        (BinaryWeightCoordinates.readWork (colors security) order arity.val.1.val arity.val.2.val) := by
  exact BinaryPairedTensor.current_bounds references.primary references.center references.anchor references.activation
    (⟨0, colors_pos security⟩, ⟨0, colors_pos security⟩) referenceHeight arity.val.1.val tableHeight
    (BinaryWeightCoordinates.readWork (colors security) order arity.val.1.val arity.val.2.val) _ groups hp hb ha hr
    (fun primary => BinaryWeightCoordinates.read_height _ _ _ _ _ _ _ _ _ tableHeight ht)
    (fun primary => BinaryWeightCoordinates.read_work _ _ _ _ _ _ _ _ _)

end CurrentAFT.BinaryWeightLocal

import CurrentAFT.BinaryWeightBlock
import CurrentAFT.PhysicalPolynomialAverages

/-! # The complete current binary physical-weight evaluator

The full joint table is supplied by the matrix iteration.  References,
primary tensor contraction, both distinct-pool averages and all arities are
executed, with no unit-cost joint-kernel oracle.
-/
namespace CurrentAFT.BinaryWeightProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra ControlCoordinates
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter lessCounter PublicParameterProgram.modulus BinaryWeightBlock.current BinaryReferenceTables.current BinaryWeightBlock.height BinaryWeightBlock.work

def term (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (references : BinaryReferenceTables.Result security) (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) (r s : Fin (order+1)) : RationalResult :=
  let degree := addCounter r.val s.val
  let allowed := lessCounter degree.count (order+1)
  let result := if h : allowed.value = true then
    BinaryWeightBlock.current security bits order primaryPool bodyPool hp hb references table
      ⟨(r, s), by change r.val+s.val ≤ order; have hd := (lessCounter_value _ _).mp h; rw [addCounter_value] at hd; omega⟩ groups centers
    else ⟨zero, 1⟩
  ⟨result.data, degree.work+allowed.work+result.work+3⟩

def current (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) : RationalResult :=
  let references := BinaryReferenceTables.current security bits
  let result := sumFin (order+1) (fun r => sumFin (order+1) (term security bits order primaryPool bodyPool hp hb references table groups centers r))
  ⟨result.data, references.work+result.work+2⟩

noncomputable section
open scoped Classical

def idealBlock (security bits order primaryPool bodyPool : ℕ)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) (arity : TruncatedArity order) : ℚ :=
  RationalWeightProgram.average arity.val.1.val arity.val.2.val primaryPool bodyPool
    (fun selected selectedCenters => RationalWeightProgram.pairedTensor security bits arity.val.1.val
      (fun primary => rawTable security order table arity primary selectedCenters) selected)
    (fun index => ((groups.get index).1.val, (groups.get index).2.val)) (fun index => (centers.get index).val)

theorem term_value (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) (r s : Fin (order+1)) :
    (term security bits order primaryPool bodyPool hp hb (BinaryReferenceTables.current security bits) table groups centers r s).data.decode =
      if h : r.val+s.val ≤ order then idealBlock security bits order primaryPool bodyPool table groups centers ⟨(r, s), h⟩ else 0 := by
  have ha : (lessCounter (addCounter r.val s.val).count (order+1)).value = true ↔ r.val+s.val ≤ order := by
    rw [lessCounter_value, addCounter_value]
    omega
  unfold term
  dsimp only
  by_cases hd : r.val+s.val ≤ order
  · simp only [dif_pos (ha.mpr hd), dif_pos hd]
    exact BinaryWeightBlock.current_value security bits order primaryPool bodyPool hp hb table ⟨(r, s), hd⟩ groups centers
  · simp only [dif_neg (fun h => hd (ha.mp h)), dif_neg hd, zero_value]

theorem current_value_sum (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) :
    (current security bits order primaryPool bodyPool hp hb table groups centers).data.decode =
      ∑ arity : TruncatedArity order, idealBlock security bits order primaryPool bodyPool table groups centers arity := by
  rw [current, sumFin_value]
  simp_rw [sumFin_value, term_value]
  have hsum := Finset.sum_subtype (p := fun pair : Fin (order+1) × Fin (order+1) => pair.1.val+pair.2.val ≤ order)
    (F := inferInstance) (Finset.univ.filter (fun pair => pair.1.val+pair.2.val ≤ order)) (by simp)
    (fun pair => if h : pair.1.val+pair.2.val ≤ order then
      idealBlock security bits order primaryPool bodyPool table groups centers ⟨pair, h⟩ else 0)
  rw [Finset.sum_filter] at hsum
  have hh : (∑ pair : Fin (order+1) × Fin (order+1),
      if h : pair.1.val+pair.2.val ≤ order then idealBlock security bits order primaryPool bodyPool table groups centers ⟨pair, h⟩ else 0) =
      ∑ arity : TruncatedArity order, idealBlock security bits order primaryPool bodyPool table groups centers arity := by
    convert hsum using 1
    · apply Finset.sum_congr rfl
      intro pair _
      by_cases hd : pair.1.val+pair.2.val ≤ order <;> simp [hd]
    · apply Finset.sum_congr rfl
      intro arity _
      rw [dif_pos arity.property]
  exact (Fintype.sum_prod_type _).symm.trans hh

private theorem average_zero (primaryPool bodyPool : ℕ) (kernel : (Fin 0 → ℕ × ℕ) → (Fin 0 → ℕ) → ℚ)
    (groups : Fin primaryPool → ℕ × ℕ) (centers : Fin bodyPool → ℕ) :
    RationalWeightProgram.average 0 0 primaryPool bodyPool kernel groups centers = kernel Fin.elim0 Fin.elim0 := by
  letI := CyclePatternProgram.selectionFintype primaryPool 0
  letI := CyclePatternProgram.selectionFintype bodyPool 0
  let first : Fin 0 ↪ Fin primaryPool := ⟨Fin.elim0, fun index => Fin.elim0 index⟩
  let second : Fin 0 ↪ Fin bodyPool := ⟨Fin.elim0, fun index => Fin.elim0 index⟩
  unfold RationalWeightProgram.average
  simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, div_one]
  rw [Fintype.sum_subsingleton _ (first, second)]
  exact congrArg₂ kernel (Subsingleton.elim _ _) (Subsingleton.elim _ _)

theorem current_value (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) :
    (current security bits order primaryPool bodyPool hp hb table groups centers).data.decode =
      RationalWeightProgram.current security bits order primaryPool bodyPool (rawTable security order table)
        (fun index => ((groups.get index).1.val, (groups.get index).2.val)) (fun index => (centers.get index).val) := by
  rw [current_value_sum, PhysicalPolynomialAverages.sum_arities]
  unfold RationalWeightProgram.current
  apply congrArg₂ (·+·)
  · unfold idealBlock
    simp only [zeroArity, Fin.val_zero]
    rw [average_zero, RationalWeightProgram.pairedTensor]
  · rfl

def blockHeightSum (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  ∑ arity : TruncatedArity order,
    BinaryWeightBlock.height security primaryPool bodyPool referenceHeight tableHeight arity.val.1.val arity.val.2.val

def blockWorkSum (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  ∑ arity : TruncatedArity order,
    BinaryWeightBlock.work security order primaryPool bodyPool referenceHeight tableHeight arity.val.1.val arity.val.2.val

def termWork (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  blockWorkSum security order primaryPool bodyPool referenceHeight tableHeight+5*order+11

def outputHeight (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  let inner := (order+1)*(blockHeightSum security order primaryPool bodyPool referenceHeight tableHeight+1)
  (order+1)*(inner+1)

def evaluationWork (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  let H := blockHeightSum security order primaryPool bodyPool referenceHeight tableHeight
  let K := termWork security order primaryPool bodyPool referenceHeight tableHeight
  let innerH := (order+1)*(H+1)
  let innerW := (order+1)*(K+primitiveWorkBound ((order+2)*(H+1))+2)+2
  (order+1)*(innerW+primitiveWorkBound ((order+2)*(innerH+1))+2)+2

theorem term_bounds (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (references : BinaryReferenceTables.Result security) (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) (r s : Fin (order+1)) (referenceHeight tableHeight : ℕ)
    (hprimary : ∀ color, HeightBound (references.primary.get color).decode referenceHeight)
    (hbody : ∀ color, HeightBound (references.center.get color).decode referenceHeight)
    (ha : ∀ input output, HeightBound ((references.anchor.get input).get output).decode referenceHeight)
    (hr : HeightBound references.activation.decode referenceHeight)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode tableHeight) :
    HeightBound (term security bits order primaryPool bodyPool hp hb references table groups centers r s).data.decode
      (blockHeightSum security order primaryPool bodyPool referenceHeight tableHeight) ∧
    (term security bits order primaryPool bodyPool hp hb references table groups centers r s).work ≤
      termWork security order primaryPool bodyPool referenceHeight tableHeight := by
  have wa : (addCounter r.val s.val).work ≤ 2*order+1 :=
    (addCounter_work r.val s.val).le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ r.isLt)) 1)
  have wl : (lessCounter (addCounter r.val s.val).count (order+1)).work ≤ 3*(order+1)+2 := lessCounter_work_right _ _
  unfold term
  dsimp only
  by_cases h : (lessCounter (addCounter r.val s.val).count (order+1)).value = true
  · have hd : r.val+s.val ≤ order := by
      have hh := (lessCounter_value _ _).mp h
      rw [addCounter_value] at hh
      omega
    simp only [dif_pos h]
    have hx := BinaryWeightBlock.current_bounds security bits order primaryPool bodyPool hp hb references table
      ⟨(r, s), hd⟩ groups centers referenceHeight tableHeight hprimary hbody ha hr ht
    have bh : BinaryWeightBlock.height security primaryPool bodyPool referenceHeight tableHeight r.val s.val ≤
        blockHeightSum security order primaryPool bodyPool referenceHeight tableHeight :=
      Finset.single_le_sum (f := fun arity : TruncatedArity order =>
        BinaryWeightBlock.height security primaryPool bodyPool referenceHeight tableHeight arity.val.1.val arity.val.2.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨(r, s), hd⟩ : TruncatedArity order))
    have bw : BinaryWeightBlock.work security order primaryPool bodyPool referenceHeight tableHeight r.val s.val ≤
        blockWorkSum security order primaryPool bodyPool referenceHeight tableHeight :=
      Finset.single_le_sum (f := fun arity : TruncatedArity order =>
        BinaryWeightBlock.work security order primaryPool bodyPool referenceHeight tableHeight arity.val.1.val arity.val.2.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨(r, s), hd⟩ : TruncatedArity order))
    exact ⟨hx.1.mono bh, by unfold termWork; have wx := hx.2.trans bw; omega⟩
  · simp only [dif_neg h]
    exact ⟨by rw [zero_value]; exact HeightBound.zero.mono (Nat.zero_le _), by unfold termWork; omega⟩

theorem current_bounds (security order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (precision : Polynomial ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) (tableHeight : ℕ)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode tableHeight) :
    HeightBound (current security (precision.eval security) order primaryPool bodyPool hp hb table groups centers).data.decode
      (outputHeight security order primaryPool bodyPool ((BinaryReferenceTables.heightPolynomial precision).eval security) tableHeight) ∧
    (current security (precision.eval security) order primaryPool bodyPool hp hb table groups centers).work ≤
      (BinaryReferenceTables.currentWorkPolynomial precision).eval security+
        evaluationWork security order primaryPool bodyPool ((BinaryReferenceTables.heightPolynomial precision).eval security) tableHeight+2 := by
  let references := BinaryReferenceTables.current security (precision.eval security)
  let H := blockHeightSum security order primaryPool bodyPool ((BinaryReferenceTables.heightPolynomial precision).eval security) tableHeight
  let K := termWork security order primaryPool bodyPool ((BinaryReferenceTables.heightPolynomial precision).eval security) tableHeight
  have href := BinaryReferenceTables.current_bounds security precision
  have hterm (r s : Fin (order+1)) := term_bounds security (precision.eval security) order primaryPool bodyPool hp hb references table groups centers r s
    ((BinaryReferenceTables.heightPolynomial precision).eval security) tableHeight href.1 href.2.1 href.2.2.1 href.2.2.2.1 ht
  have hinner (r : Fin (order+1)) := sumFin_height (order+1) H
    (term security (precision.eval security) order primaryPool bodyPool hp hb references table groups centers r)
    (fun s => (hterm r s).1)
  have winner (r : Fin (order+1)) := sumFin_work (order+1) H K
    (term security (precision.eval security) order primaryPool bodyPool hp hb references table groups centers r)
    (fun s => (hterm r s).1) (fun s => (hterm r s).2)
  have hout := sumFin_height (order+1) ((order+1)*(H+1))
    (fun r => sumFin (order+1) (term security (precision.eval security) order primaryPool bodyPool hp hb references table groups centers r)) hinner
  have wout := sumFin_work (order+1) ((order+1)*(H+1))
    ((order+1)*(K+primitiveWorkBound ((order+1+1)*(H+1))+2)+2)
    (fun r => sumFin (order+1) (term security (precision.eval security) order primaryPool bodyPool hp hb references table groups centers r))
    hinner winner
  constructor
  · exact hout
  · change references.work+_+2 ≤ _
    apply Nat.add_le_add_right (Nat.add_le_add href.2.2.2.2 ?_) 2
    simpa only [evaluationWork, H, K, Nat.add_assoc, Nat.reduceAdd] using wout

end
end CurrentAFT.BinaryWeightProgram

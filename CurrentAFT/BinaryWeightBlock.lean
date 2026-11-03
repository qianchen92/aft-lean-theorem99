import CurrentAFT.BinaryWeightLocal
import CurrentAFT.BinaryTwoPoolAverage

/-! # The full two-pool physical weight contribution of one joint block -/
namespace CurrentAFT.BinaryWeightBlock
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryWeightLocal.current BinaryTwoPoolAverage.current BinaryReferenceTables.current

def selected (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (references : BinaryReferenceTables.Result security) (table : BinaryWeightCoordinates.Table (colors security) order)
    (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool)
    (first : Vector (Fin primaryPool) arity.val.1.val) (second : Vector (Fin bodyPool) arity.val.2.val) : RationalResult :=
  let gs := gather (⟨0, colors_pos security⟩, ⟨0, colors_pos security⟩) hp groups first
  let bs := gather ⟨0, colors_pos security⟩ hb centers second
  let result := BinaryWeightLocal.current security bits order references table arity gs.value bs.value
  ⟨result.data, gs.work+bs.work+result.work+3⟩

def current (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (references : BinaryReferenceTables.Result security) (table : BinaryWeightCoordinates.Table (colors security) order)
    (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) : RationalResult :=
  BinaryTwoPoolAverage.current primaryPool bodyPool arity.val.1.val arity.val.2.val hp hb
    (selected security bits order primaryPool bodyPool hp hb references table arity groups centers)

def localHeight (security referenceHeight tableHeight r : ℕ) : ℕ := BinaryPairedTensor.height (colors security) referenceHeight r tableHeight

def localWork (security order primaryPool bodyPool referenceHeight tableHeight r s : ℕ) : ℕ :=
  gatherWork primaryPool r+gatherWork bodyPool s+
    BinaryPairedTensor.work (colors security) referenceHeight r tableHeight
      (BinaryWeightCoordinates.readWork (colors security) order r s)+3

def height (security primaryPool bodyPool referenceHeight tableHeight r s : ℕ) : ℕ :=
  BinaryTwoPoolAverage.height primaryPool bodyPool r s (localHeight security referenceHeight tableHeight r)

def work (security order primaryPool bodyPool referenceHeight tableHeight r s : ℕ) : ℕ :=
  BinaryTwoPoolAverage.work primaryPool bodyPool r s (localHeight security referenceHeight tableHeight r)
    (localWork security order primaryPool bodyPool referenceHeight tableHeight r s)

noncomputable section
open scoped Classical

theorem selected_value (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order) (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool)
    (first : Vector (Fin primaryPool) arity.val.1.val) (second : Vector (Fin bodyPool) arity.val.2.val) :
    (selected security bits order primaryPool bodyPool hp hb (BinaryReferenceTables.current security bits) table arity groups centers first second).data.decode =
      RationalWeightProgram.pairedTensor security bits arity.val.1.val
        (fun primary => rawTable security order table arity primary (fun index => (centers.get (second.get index)).val))
        (fun index => ((groups.get (first.get index)).1.val, (groups.get (first.get index)).2.val)) := by
  unfold selected
  rw [BinaryWeightLocal.current_value]
  simp only [gather_get]

theorem current_value (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order) (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) :
    (current security bits order primaryPool bodyPool hp hb (BinaryReferenceTables.current security bits) table arity groups centers).data.decode =
      RationalWeightProgram.average arity.val.1.val arity.val.2.val primaryPool bodyPool
        (fun selected selectedCenters => RationalWeightProgram.pairedTensor security bits arity.val.1.val
          (fun primary => rawTable security order table arity primary selectedCenters) selected)
        (fun index => ((groups.get index).1.val, (groups.get index).2.val)) (fun index => (centers.get index).val) := by
  rw [current, BinaryTwoPoolAverage.current_value]
  simp_rw [selected_value]
  simp only [Vector.get_ofFn]
  unfold RationalWeightProgram.average
  apply congrArg (fun numerator : ℚ => numerator /
    ((primaryPool.descFactorial arity.val.1.val:ℚ)*(bodyPool.descFactorial arity.val.2.val:ℚ)))
  letI := CyclePatternProgram.selectionFintype primaryPool arity.val.1.val
  letI := CyclePatternProgram.selectionFintype bodyPool arity.val.2.val
  have hprod : (∑ pair : (Fin arity.val.1.val ↪ Fin primaryPool) × (Fin arity.val.2.val ↪ Fin bodyPool),
      RationalWeightProgram.pairedTensor security bits arity.val.1.val
        (fun primary => rawTable security order table arity primary (fun index => (centers.get (pair.2 index)).val))
        (fun index => ((groups.get (pair.1 index)).1.val, (groups.get (pair.1 index)).2.val))) =
      ∑ first : Fin arity.val.1.val ↪ Fin primaryPool, ∑ second : Fin arity.val.2.val ↪ Fin bodyPool,
        RationalWeightProgram.pairedTensor security bits arity.val.1.val
          (fun primary => rawTable security order table arity primary (fun index => (centers.get (second index)).val))
          (fun index => ((groups.get (first index)).1.val, (groups.get (first index)).2.val)) := by
    rw [Fintype.sum_prod_type]
  apply Eq.trans ?_ hprod.symm
  apply Finset.sum_congr (by ext; simp)
  intro first _
  apply Finset.sum_congr (by ext; simp)
  intro second _
  rfl

theorem current_bounds (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (references : BinaryReferenceTables.Result security) (table : BinaryWeightCoordinates.Table (colors security) order)
    (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) (referenceHeight tableHeight : ℕ)
    (hprimary : ∀ color, HeightBound (references.primary.get color).decode referenceHeight)
    (hbody : ∀ color, HeightBound (references.center.get color).decode referenceHeight)
    (ha : ∀ input output, HeightBound ((references.anchor.get input).get output).decode referenceHeight)
    (hr : HeightBound references.activation.decode referenceHeight)
    (ht : ∀ block word, HeightBound ((table.get block).get word).decode tableHeight) :
    HeightBound (current security bits order primaryPool bodyPool hp hb references table arity groups centers).data.decode
      (height security primaryPool bodyPool referenceHeight tableHeight arity.val.1.val arity.val.2.val) ∧
    (current security bits order primaryPool bodyPool hp hb references table arity groups centers).work ≤
      work security order primaryPool bodyPool referenceHeight tableHeight arity.val.1.val arity.val.2.val := by
  unfold current height work localHeight localWork
  refine BinaryTwoPoolAverage.current_bounds primaryPool bodyPool arity.val.1.val arity.val.2.val hp hb
    (selected security bits order primaryPool bodyPool hp hb references table arity groups centers)
    (BinaryPairedTensor.height (colors security) referenceHeight arity.val.1.val tableHeight)
    (gatherWork primaryPool arity.val.1.val+gatherWork bodyPool arity.val.2.val+
      BinaryPairedTensor.work (colors security) referenceHeight arity.val.1.val tableHeight
        (BinaryWeightCoordinates.readWork (colors security) order arity.val.1.val arity.val.2.val)+3) ?_ ?_
  · intro first second
    simp only [selected]
    exact (BinaryWeightLocal.current_bounds security bits order references table arity
      (gather (⟨0, colors_pos security⟩, ⟨0, colors_pos security⟩) hp groups first).value
      (gather ⟨0, colors_pos security⟩ hb centers second).value referenceHeight tableHeight
      hprimary hbody ha hr ht).1
  · intro first second
    have wlocal := (BinaryWeightLocal.current_bounds security bits order references table arity
      (gather (⟨0, colors_pos security⟩, ⟨0, colors_pos security⟩) hp groups first).value
      (gather ⟨0, colors_pos security⟩ hb centers second).value referenceHeight tableHeight
      hprimary hbody ha hr ht).2
    have wg := gather_work (⟨0, colors_pos security⟩, ⟨0, colors_pos security⟩) hp groups first
    have wb := gather_work ⟨0, colors_pos security⟩ hb centers second
    simp only [selected]
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add wg wb) wlocal) 3

end
end CurrentAFT.BinaryWeightBlock

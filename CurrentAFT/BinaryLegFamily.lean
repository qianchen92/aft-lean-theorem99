import CurrentAFT.BinaryLegSelectedCoefficient
import CurrentAFT.BinarySubsetCoefficientSum
import CurrentAFT.BinaryFamilyPower

/-! # All eight stored subsets of the actual three-endpoint joint mass -/
namespace CurrentAFT.BinaryLegFamily
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
open BinaryLegSelectedCoefficient
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def guarded (security bits order lower : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let shape := lessCounter (lower-1) entry.selected.card
    if shape.value then
      let result := BinaryLegSelectedCoefficient.current security bits order entry mass arity colors centers
      ⟨result.value,shape.work+result.work+2⟩
    else ⟨zero,shape.work+2⟩

def sum (security bits order lower : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) : CoefficientProgram order :=
  BinarySubsetCoefficientSum.current order fallback entries (fun entry => guarded security bits order lower entry mass)

def higher (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) : CoefficientProgram order :=
  sum security bits order 2 fallback entries mass

def positive (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let unit := BinaryFamilyPower.unit order arity colors centers
    let terms := sum security bits order 1 fallback entries mass arity colors centers
    let result := RationalBits.add unit.value terms.value
    ⟨result.data,unit.work+terms.work+result.work+2⟩

noncomputable section
open scoped Classical

theorem guarded_value (security bits order lower : ℕ) (hlower : 1≤lower) (entry : Entry) (hvalid : Valid entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult)
    (value : (Fin 3 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (guarded security bits order lower entry mass arity colors centers).value.decode=
      if lower≤entry.selected.card then
        RationalLegFamilyTable.insertSelected order entry.selected
          (RationalLegCoefficientExtraction.selectedKernel security bits value entry.selected) arity colors.get centers.get else 0 := by
  have hshape : (lessCounter (lower-1) entry.selected.card).value=true ↔ lower≤entry.selected.card := by
    rw [lessCounter_value]
    omega
  by_cases ht : (lessCounter (lower-1) entry.selected.card).value=true
  · simp only [guarded,if_pos ht,if_pos (hshape.mp ht)]
    exact BinaryLegSelectedCoefficient.current_value security bits order entry hvalid.1 hvalid.2 mass value hmass arity colors centers hc hd
  · simp only [guarded,if_neg ht,if_neg (fun h => ht (hshape.mpr h)),zero_value]

theorem sum_value (security bits order lower : ℕ) (hlower : 1≤lower) (fallback : Entry) (entries : Vector Entry 8)
    (ordering : Fin 8 ≃ Finset (Fin 3)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, Valid (entries.get index))
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult)
    (value : (Fin 3 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (sum security bits order lower fallback entries mass arity colors centers).value.decode=
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => lower≤selected.card),
        RationalLegFamilyTable.insertSelected order selected
          (RationalLegCoefficientExtraction.selectedKernel security bits value selected) arity colors.get centers.get := by
  rw [sum,BinarySubsetCoefficientSum.current_value order (BinaryFirstInverseProgram.colors security) fallback entries
    (fun entry => guarded security bits order lower entry mass)
    (fun entry arity colors centers => if lower≤entry.selected.card then
      RationalLegFamilyTable.insertSelected order entry.selected
        (RationalLegCoefficientExtraction.selectedKernel security bits value entry.selected) arity colors centers else 0)
    (fun index => guarded_value security bits order lower hlower (entries.get index) (hvalid index) mass value hmass) arity colors centers hc hd]
  let term := fun selected : Finset (Fin 3) => if lower≤selected.card then
    RationalLegFamilyTable.insertSelected order selected
      (RationalLegCoefficientExtraction.selectedKernel security bits value selected) arity colors.get centers.get else 0
  change (∑ index, term (entries.get index).selected)=_
  calc
    _ = ∑ index, term (ordering index) := Finset.sum_congr rfl (fun index _ => congrArg term (hselected index))
    _ = ∑ selected, term selected := ordering.sum_comp term
    _ = _ := by rw [Finset.sum_filter]

theorem higher_value (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (ordering : Fin 8 ≃ Finset (Fin 3)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, Valid (entries.get index))
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult)
    (value : (Fin 3 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (higher security bits order fallback entries mass arity colors centers).value.decode=
      RationalLegFamilyTable.higher security bits order value arity colors.get centers.get :=
  sum_value security bits order 2 (by norm_num) fallback entries ordering hselected hvalid mass value hmass arity colors centers hc hd

theorem positive_value (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (ordering : Fin 8 ≃ Finset (Fin 3)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, Valid (entries.get index))
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult)
    (value : (Fin 3 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (positive security bits order fallback entries mass arity colors centers).value.decode=
      RationalLegFamilyTable.positive security bits order value arity colors.get centers.get := by
  rw [positive,RationalBits.add_value,BinaryFamilyPower.unit_value,
    sum_value security bits order 1 (by norm_num) fallback entries ordering hselected hvalid mass value hmass arity colors centers hc hd]
  have heq : (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 1≤selected.card)=
      (Finset.univ : Finset (Finset (Fin 3))).erase ∅ := by
    ext selected
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,ne_eq,and_true]
    exact Finset.card_pos.trans Finset.nonempty_iff_ne_empty
  rw [heq]
  rfl

end
end CurrentAFT.BinaryLegFamily

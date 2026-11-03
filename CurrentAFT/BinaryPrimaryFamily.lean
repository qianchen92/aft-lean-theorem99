import CurrentAFT.BinaryPrimarySelectedCoefficient
import CurrentAFT.BinarySubsetCoefficientSum
import CurrentAFT.BinaryFamilyPower

/-! # All sixteen stored subsets of the actual four-endpoint joint mass -/
namespace CurrentAFT.BinaryPrimaryFamily
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
open BinaryPrimarySelectedCoefficient
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def guarded (security bits order lower : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let shape := lessCounter (lower-1) entry.selected.card
    if shape.value then
      let result := BinaryPrimarySelectedCoefficient.current security bits order entry mass arity colors centers
      ⟨result.value,shape.work+result.work+2⟩
    else ⟨zero,shape.work+2⟩

def sum (security bits order lower : ℕ) (fallback : Entry) (entries : Vector Entry 16)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) : CoefficientProgram order :=
  BinarySubsetCoefficientSum.current order fallback entries (fun entry => guarded security bits order lower entry mass)

def higher (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 16)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) : CoefficientProgram order :=
  sum security bits order 2 fallback entries mass

def positive (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 16)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let unit := BinaryFamilyPower.unit order arity colors centers
    let terms := sum security bits order 1 fallback entries mass arity colors centers
    let result := RationalBits.add unit.value terms.value
    ⟨result.data,unit.work+terms.work+result.work+2⟩

noncomputable section
open scoped Classical

theorem guarded_value (security bits order lower : ℕ) (hlower : 1≤lower) (entry : Entry) (hvalid : Valid entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult)
    (value : (Fin 4 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (guarded security bits order lower entry mass arity colors centers).value.decode=
      if lower≤entry.selected.card then
        RationalLocalFamilyProgram.insertSelected order entry.selected
          (RationalCoefficientExtraction.selectedKernel security bits value entry.selected) arity colors.get centers.get else 0 := by
  have hshape : (lessCounter (lower-1) entry.selected.card).value=true ↔ lower≤entry.selected.card := by
    rw [lessCounter_value]
    omega
  by_cases ht : (lessCounter (lower-1) entry.selected.card).value=true
  · simp only [guarded,if_pos ht,if_pos (hshape.mp ht)]
    exact BinaryPrimarySelectedCoefficient.current_value security bits order entry hvalid.1 hvalid.2 mass value hmass arity colors centers hc hd
  · simp only [guarded,if_neg ht,if_neg (fun h => ht (hshape.mpr h)),zero_value]

theorem sum_value (security bits order lower : ℕ) (hlower : 1≤lower) (fallback : Entry) (entries : Vector Entry 16)
    (ordering : Fin 16 ≃ Finset (Fin 4)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, Valid (entries.get index))
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult)
    (value : (Fin 4 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (sum security bits order lower fallback entries mass arity colors centers).value.decode=
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => lower≤selected.card),
        RationalLocalFamilyProgram.insertSelected order selected
          (RationalCoefficientExtraction.selectedKernel security bits value selected) arity colors.get centers.get := by
  rw [sum,BinarySubsetCoefficientSum.current_value order (BinaryFirstInverseProgram.colors security) fallback entries
    (fun entry => guarded security bits order lower entry mass)
    (fun entry arity colors centers => if lower≤entry.selected.card then
      RationalLocalFamilyProgram.insertSelected order entry.selected
        (RationalCoefficientExtraction.selectedKernel security bits value entry.selected) arity colors centers else 0)
    (fun index => guarded_value security bits order lower hlower (entries.get index) (hvalid index) mass value hmass) arity colors centers hc hd]
  let term := fun selected : Finset (Fin 4) => if lower≤selected.card then
    RationalLocalFamilyProgram.insertSelected order selected
      (RationalCoefficientExtraction.selectedKernel security bits value selected) arity colors.get centers.get else 0
  change (∑ index, term (entries.get index).selected)=_
  calc
    _ = ∑ index, term (ordering index) := Finset.sum_congr rfl (fun index _ => congrArg term (hselected index))
    _ = ∑ selected, term selected := ordering.sum_comp term
    _ = _ := by rw [Finset.sum_filter]

theorem positive_value (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 16)
    (ordering : Fin 16 ≃ Finset (Fin 4)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, Valid (entries.get index))
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult)
    (value : (Fin 4 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (positive security bits order fallback entries mass arity colors centers).value.decode=
      RationalFamilyProductProgram.unit order arity colors.get centers.get +
        ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
          RationalLocalFamilyProgram.insertSelected order selected
            (RationalCoefficientExtraction.selectedKernel security bits value selected) arity colors.get centers.get := by
  rw [positive,RationalBits.add_value,BinaryFamilyPower.unit_value,
    sum_value security bits order 1 (by norm_num) fallback entries ordering hselected hvalid mass value hmass arity colors centers hc hd]
  have heq : (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 1≤selected.card)=
      (Finset.univ : Finset (Finset (Fin 4))).erase ∅ := by
    ext selected
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,ne_eq,and_true]
    exact Finset.card_pos.trans Finset.nonempty_iff_ne_empty
  rw [heq]

noncomputable def leafHeight (entries : Vector Entry 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  ∑ index : Fin 16, BinaryPrimarySelectedCoefficient.heightPolynomial (entries.get index) precision inputBits
noncomputable def leafWork (order lower : ℕ) (entries : Vector Entry 16) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (3*lower+4)+∑ index : Fin 16,
    BinaryPrimarySelectedCoefficient.workPolynomial order (entries.get index) precision inputBits inputWork
noncomputable def heightPolynomial (entries : Vector Entry 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinarySubsetCoefficientSum.heightPolynomial 16 (leafHeight entries precision inputBits)
noncomputable def workPolynomial (order lower : ℕ) (entries : Vector Entry 16) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinarySubsetCoefficientSum.workPolynomial 16 (leafHeight entries precision inputBits) (leafWork order lower entries precision inputBits inputWork)

theorem sum_bounds (security order lower : ℕ) (fallback : Entry) (entries : Vector Entry 16)
    (precision inputBits inputWork : Polynomial ℕ)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (sum security (precision.eval security) order lower fallback entries mass arity colors centers).value.decode
      ((heightPolynomial entries precision inputBits).eval security) ∧
      (sum security (precision.eval security) order lower fallback entries mass arity colors centers).work ≤
        (workPolynomial order lower entries precision inputBits inputWork).eval security := by
  refine BinarySubsetCoefficientSum.current_bounds order (BinaryFirstInverseProgram.colors security) security fallback entries
    (fun entry => guarded security (precision.eval security) order lower entry mass)
    (leafHeight entries precision inputBits) (leafWork order lower entries precision inputBits inputWork) ?_ arity colors centers hc hd
  intro index arity colors centers hc hd
  have he := BinaryPrimarySelectedCoefficient.current_bounds security order (entries.get index) precision inputBits inputWork mass hh hw arity colors centers hc hd
  have hheight : (BinaryPrimarySelectedCoefficient.heightPolynomial (entries.get index) precision inputBits).eval security ≤
      (leafHeight entries precision inputBits).eval security := by
    rw [leafHeight,Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (f := fun index : Fin 16 =>
      (BinaryPrimarySelectedCoefficient.heightPolynomial (entries.get index) precision inputBits).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hwork : (BinaryPrimarySelectedCoefficient.workPolynomial order (entries.get index) precision inputBits inputWork).eval security+3*lower+4 ≤
      (leafWork order lower entries precision inputBits inputWork).eval security := by
    simp only [leafWork,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_finset_sum]
    have hs := Finset.single_le_sum (f := fun index : Fin 16 =>
      (BinaryPrimarySelectedCoefficient.workPolynomial order (entries.get index) precision inputBits inputWork).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Nat.add_le_add_left hs (3*lower+4)
  have wg := lessCounter_work_left (lower-1) (entries.get index).selected.card
  by_cases hs : (lessCounter (lower-1) (entries.get index).selected.card).value=true
  · simp only [guarded,if_pos hs]
    exact ⟨he.1.mono hheight,by omega⟩
  · simp only [guarded,if_neg hs,zero_value]
    exact ⟨HeightBound.zero.mono (Nat.zero_le _),by omega⟩

noncomputable def positiveHeightPolynomial (entries : Vector Entry 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  heightPolynomial entries precision inputBits+1
noncomputable def positiveWorkPolynomial (order : ℕ) (entries : Vector Entry 16) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (12*order+10)+workPolynomial order 1 entries precision inputBits inputWork+
    primitiveWorkPolynomial (heightPolynomial entries precision inputBits)

theorem positive_bounds (security order : ℕ) (fallback : Entry) (entries : Vector Entry 16)
    (precision inputBits inputWork : Polynomial ℕ)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (positive security (precision.eval security) order fallback entries mass arity colors centers).value.decode
      ((positiveHeightPolynomial entries precision inputBits).eval security) ∧
      (positive security (precision.eval security) order fallback entries mass arity colors centers).work ≤
        (positiveWorkPolynomial order entries precision inputBits inputWork).eval security := by
  have hs := sum_bounds security order 1 fallback entries precision inputBits inputWork mass hh hw arity colors centers hc hd
  have hu := BinaryFamilyPower.unit_bounds order arity colors centers
  constructor
  · simp only [positive,RationalBits.add_value,positiveHeightPolynomial,Polynomial.eval_add,Polynomial.eval_one]
    exact (hu.1.add hs.1).mono (by omega)
  · have wa := RationalBits.add_work (BinaryFamilyPower.unit order arity colors centers).value
      (sum security (precision.eval security) order 1 fallback entries mass arity colors centers).value
      ((heightPolynomial entries precision inputBits).eval security) (hu.1.mono (Nat.zero_le _)) hs.1
    change _+_+_+2 ≤ _
    simp only [positiveWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C,primitiveWorkPolynomial_eval]
    omega

end
end CurrentAFT.BinaryPrimaryFamily

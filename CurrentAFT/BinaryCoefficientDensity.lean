import CurrentAFT.BinaryCoefficientAtom
import CurrentAFT.BinaryDensityInverseTensor

/-! Complete four-endpoint coefficient extraction. The selected slots are
stored fixed metadata; all four source colors are summed jointly. -/
namespace CurrentAFT.BinaryCoefficientDensity
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryCoefficientAtom.current BinaryFiniteProduct.current BinaryTupleSum.current
variable {totalSlots : ℕ}

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def column {degree : ℕ} (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (source : Vector (Fin (colors security)) totalSlots) (output : Vector (Fin (colors security)) degree) (index : Fin degree) : RationalResult :=
  let position := readVector ⟨0, by have h := (slots.get index).isLt; omega⟩ slots index
  let input := readVector (BinaryDensityInverseTensor.first security) source position.value
  let value := readVector (BinaryDensityInverseTensor.first security) output index
  let result := BinaryCoefficientAtom.current security bits input.value value.value
  ⟨result.data,position.work+input.work+value.work+result.work+4⟩

theorem column_value {degree : ℕ} (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (source : Vector (Fin (colors security)) totalSlots) (output : Vector (Fin (colors security)) degree) (index : Fin degree) :
    (column security bits slots source output index).data.decode =
      RationalCoefficientExtraction.atom security bits (source.get (slots.get index)).val (output.get index).val := by
  simp only [column, BinaryCoefficientAtom.current_value, readVector_value]

def term {degree : ℕ} (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (output : Vector (Fin (colors security)) degree)
    (mass : Vector (Fin (colors security)) totalSlots → RationalResult) (source : Vector (Fin (colors security)) totalSlots) : RationalResult :=
  let value := mass source
  let product := BinaryFiniteProduct.current degree (column security bits slots source output)
  let result := RationalBits.multiply value.data product.data
  ⟨result.data,value.work+product.work+result.work+3⟩

theorem term_value {degree : ℕ} (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (output : Vector (Fin (colors security)) degree)
    (mass : Vector (Fin (colors security)) totalSlots → RationalResult) (source : Vector (Fin (colors security)) totalSlots) :
    (term security bits slots output mass source).data.decode = (mass source).data.decode*
      ∏ index, RationalCoefficientExtraction.atom security bits (source.get (slots.get index)).val (output.get index).val := by
  simp only [term, RationalBits.multiply_value, BinaryFiniteProduct.current_value, column_value]

def current {degree : ℕ} (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (output : Vector (Fin (colors security)) degree) (mass : Vector (Fin (colors security)) totalSlots → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryTupleSum.current modulus.count totalSlots (term security bits slots output mass)
  ⟨result.data,modulus.work+result.work+2⟩

theorem sum_value {degree : ℕ} (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (output : Vector (Fin (colors security)) degree) (mass : Vector (Fin (colors security)) totalSlots → RationalResult)
    (value : (Fin totalSlots → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode = value (fun index => (source.get index).val)) :
    (current security bits slots output mass).data.decode =
      ∑ source : Fin totalSlots → Fin (colors security), value (fun index => (source index).val)*
        ∏ index, RationalCoefficientExtraction.atom security bits (source (slots.get index)).val (output.get index).val := by
  change (BinaryTupleSum.current _ _ _).data.decode = _
  rw [BinaryTupleSum.current_value]
  apply Finset.sum_congr rfl
  intro source _
  simp only [term_value, hmass, Vector.get_ofFn]

theorem current_value (security bits : ℕ) (selected : Finset (Fin 4)) (slots : Vector (Fin 4) selected.card)
    (hslots : ∀ index, slots.get index = ((Finset.orderIsoOfFin selected rfl) index).val)
    (output : Vector (Fin (colors security)) selected.card) (mass : Vector (Fin (colors security)) 4 → RationalResult)
    (value : (Fin 4 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode = value (fun index => (source.get index).val)) :
    (current security bits slots output mass).data.decode =
      RationalCoefficientExtraction.density security bits value selected (fun index => (output.get index).val) := by
  change (BinaryTupleSum.current _ _ _).data.decode = _
  rw [BinaryTupleSum.current_value]
  unfold RationalCoefficientExtraction.density
  apply Finset.sum_congr rfl
  intro source _
  simp only [term_value, hmass, Vector.get_ofFn]
  congr 1
  rw [← Equiv.prod_comp (Finset.orderIsoOfFin selected rfl).toEquiv]
  apply Finset.prod_congr rfl
  intro index _
  simp only [hslots, RationalCoefficientExtraction.slotNumber]
  change RationalCoefficientExtraction.atom security bits (source ((Finset.orderIsoOfFin selected rfl) index).val).val (output.get index).val =
    RationalCoefficientExtraction.atom security bits (source ((Finset.orderIsoOfFin selected rfl) index).val).val
      (output.get ((Finset.orderIsoOfFin selected rfl).symm ((Finset.orderIsoOfFin selected rfl) index))).val
  rw [OrderIso.symm_apply_apply]

noncomputable section

private theorem tupleHeight_mono {pool larger count firstHeight secondHeight : ℕ}
    (hp : pool ≤ larger) (hh : firstHeight ≤ secondHeight) :
    BinaryTupleSum.height pool count firstHeight ≤ BinaryTupleSum.height larger count secondHeight := by
  induction count with
  | zero => exact hh
  | succ count ih => exact Nat.mul_le_mul hp (Nat.add_le_add_right ih 1)

private theorem tupleWork_mono {pool larger count firstHeight secondHeight firstWork secondWork : ℕ}
    (hp : pool ≤ larger) (hh : firstHeight ≤ secondHeight) (hw : firstWork ≤ secondWork) :
    BinaryTupleSum.work pool count firstHeight firstWork ≤ BinaryTupleSum.work larger count secondHeight secondWork := by
  induction count generalizing firstWork secondWork with
  | zero => exact hw
  | succ count ih =>
    have ht := tupleHeight_mono (count := count) hp hh
    have hr := ih (Nat.add_le_add_right (Nat.add_le_add_left hw (BinaryTupleSum.prependWork count)) 1)
    simp only [BinaryTupleSum.work]
    exact Nat.add_le_add_right (Nat.mul_le_mul hp (Nat.add_le_add_right (Nat.add_le_add hr
      (primitiveWorkBound_mono (Nat.mul_le_mul (Nat.add_le_add_right hp 1) (Nat.add_le_add_right ht 1)))) 2)) 2

noncomputable def columnWorkPolynomial (totalSlots degree : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (6*degree+3*totalSlots+13)+BinaryCoefficientAtom.workPolynomial precision
noncomputable def termHeightPolynomial (degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  inputBits+Polynomial.C degree*BinaryCoefficientAtom.heightPolynomial precision
noncomputable def termWorkPolynomial (totalSlots degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  inputWork+BinaryFiniteProduct.workPolynomial degree (BinaryCoefficientAtom.heightPolynomial precision)
    (columnWorkPolynomial totalSlots degree precision)+primitiveWorkPolynomial (termHeightPolynomial degree precision inputBits)+3
noncomputable def heightPolynomial (totalSlots degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryTupleSum.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial totalSlots (termHeightPolynomial degree precision inputBits)
noncomputable def workPolynomial (totalSlots degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryTupleSum.workPolynomial BinaryFirstInverseProgram.colorsPolynomial totalSlots
    (termHeightPolynomial degree precision inputBits) (termWorkPolynomial totalSlots degree precision inputBits inputWork)+2

theorem column_bounds {degree : ℕ} (security : ℕ) (precision : Polynomial ℕ) (slots : Vector (Fin totalSlots) degree)
    (source : Vector (Fin (colors security)) totalSlots) (output : Vector (Fin (colors security)) degree) (index : Fin degree) :
    HeightBound (column security (precision.eval security) slots source output index).data.decode
      ((BinaryCoefficientAtom.heightPolynomial precision).eval security) ∧
      (column security (precision.eval security) slots source output index).work ≤ (columnWorkPolynomial totalSlots degree precision).eval security := by
  have h := BinaryCoefficientAtom.current_bounds security precision
    (readVector (BinaryDensityInverseTensor.first security) source (readVector (⟨0, by have h := (slots.get index).isLt; omega⟩ : Fin totalSlots) slots index).value).value
    (readVector (BinaryDensityInverseTensor.first security) output index).value
  constructor
  · exact h.1
  · have wp := readVector_work (⟨0, by have h := (slots.get index).isLt; omega⟩ : Fin totalSlots) slots index
    have wi := readVector_work (BinaryDensityInverseTensor.first security) source (readVector (⟨0, by have h := (slots.get index).isLt; omega⟩ : Fin totalSlots) slots index).value
    have wo := readVector_work (BinaryDensityInverseTensor.first security) output index
    change _+_+_+_+4 ≤ _
    simp only [columnWorkPolynomial, Polynomial.eval_add, Polynomial.eval_C]
    omega

theorem term_bounds {degree : ℕ} (security : ℕ) (precision inputBits inputWork : Polynomial ℕ)
    (slots : Vector (Fin totalSlots) degree) (output : Vector (Fin (colors security)) degree)
    (mass : Vector (Fin (colors security)) totalSlots → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security) (source : Vector (Fin (colors security)) totalSlots) :
    HeightBound (term security (precision.eval security) slots output mass source).data.decode
      ((termHeightPolynomial degree precision inputBits).eval security) ∧
      (term security (precision.eval security) slots output mass source).work ≤
        (termWorkPolynomial totalSlots degree precision inputBits inputWork).eval security := by
  let H := (termHeightPolynomial degree precision inputBits).eval security
  have hk := BinaryFiniteProduct.current_height degree ((BinaryCoefficientAtom.heightPolynomial precision).eval security)
    (column security (precision.eval security) slots source output) (fun index => (column_bounds security precision slots source output index).1)
  have wk := BinaryFiniteProduct.current_work degree ((BinaryCoefficientAtom.heightPolynomial precision).eval security)
    ((columnWorkPolynomial totalSlots degree precision).eval security) (column security (precision.eval security) slots source output)
    (fun index => (column_bounds security precision slots source output index).1) (fun index => (column_bounds security precision slots source output index).2)
  have hH : H = inputBits.eval security+degree*(BinaryCoefficientAtom.heightPolynomial precision).eval security := by
    simp only [H, termHeightPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have wm := RationalBits.multiply_work (mass source).data
    (BinaryFiniteProduct.current degree (column security (precision.eval security) slots source output)).data H
    ((hh source).mono (by rw [hH]; omega)) (hk.mono (by rw [hH]; omega))
  constructor
  · change HeightBound (RationalBits.multiply _ _).data.decode _
    rw [RationalBits.multiply_value]
    exact ((hh source).mul hk).mono (by rw [← hH])
  · have wp := hw source
    change _+_+_+3 ≤ _
    simp only [termWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat,
      BinaryFiniteProduct.workPolynomial_eval, primitiveWorkPolynomial_eval]
    change _ ≤ inputWork.eval security+BinaryFiniteProduct.work degree
      ((BinaryCoefficientAtom.heightPolynomial precision).eval security) ((columnWorkPolynomial totalSlots degree precision).eval security)+primitiveWorkBound H+3
    omega

theorem current_bounds {degree : ℕ} (security : ℕ) (precision inputBits inputWork : Polynomial ℕ)
    (slots : Vector (Fin totalSlots) degree) (output : Vector (Fin (colors security)) degree)
    (mass : Vector (Fin (colors security)) totalSlots → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security) :
    HeightBound (current security (precision.eval security) slots output mass).data.decode
      ((heightPolynomial totalSlots degree precision inputBits).eval security) ∧
      (current security (precision.eval security) slots output mass).work ≤
        (workPolynomial totalSlots degree precision inputBits inputWork).eval security := by
  have h := BinaryTupleSum.current_bounds (colors security) totalSlots
    (term security (precision.eval security) slots output mass)
    ((termHeightPolynomial degree precision inputBits).eval security)
    ((termWorkPolynomial totalSlots degree precision inputBits inputWork).eval security)
    (fun source => (term_bounds security precision inputBits inputWork slots output mass hh hw source).1)
    (fun source => (term_bounds security precision inputBits inputWork slots output mass hh hw source).2)
  have hq := BinaryFirstInverseProgram.colors_bound security
  constructor
  · change HeightBound (BinaryTupleSum.current _ _ _).data.decode _
    apply h.1.mono
    rw [heightPolynomial, BinaryTupleSum.heightPolynomial_eval]
    exact tupleHeight_mono hq (le_refl _)
  · have wq := PublicParameterProgram.modulus_work security
    have wk := h.2.trans (tupleWork_mono hq (le_refl _) (le_refl _))
    change (PublicParameterProgram.modulus security).work+(BinaryTupleSum.current (colors security) totalSlots _).work+2 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat,
      PublicParameterProgram.workPolynomial_eval, BinaryTupleSum.workPolynomial_eval]
    omega

end
end CurrentAFT.BinaryCoefficientDensity

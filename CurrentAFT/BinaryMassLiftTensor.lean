import CurrentAFT.BinaryMassLiftColumn
import CurrentAFT.BinaryFiniteProduct
import CurrentAFT.BinaryTupleSum
import CurrentAFT.RationalMassLiftTensorProgram

/-! # The full joint mass-lift tensor on explicitly enumerated binary tuples -/
namespace CurrentAFT.BinaryMassLiftTensor
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryMassLiftColumn.current BinaryFiniteProduct.current
  BinaryTupleSum.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def first (security : ℕ) : Fin (colors security) :=
  ⟨0, by rw [colors, BinaryFirstInverseProgram.colors, PublicParameterProgram.modulus_value]
         exact (Parameters.modulus_spec security).2.pos⟩

def column {degree : ℕ} (security bits : ℕ) (source output : Vector (Fin (colors security)) degree)
    (slot : Fin degree) : RationalResult :=
  let input := readVector (first security) source slot
  let result := readVector (first security) output slot
  let entry := BinaryMassLiftColumn.current security bits input.value result.value
  ⟨entry.data, input.work+result.work+entry.work+3⟩

theorem column_value {degree : ℕ} (security bits : ℕ) (source output : Vector (Fin (colors security)) degree)
    (slot : Fin degree) :
    (column security bits source output slot).data.decode =
      RationalMassLiftTensorProgram.entry security bits (source.get slot).val (output.get slot).val := by
  simp only [column, readVector_value, BinaryMassLiftColumn.current_value, RationalMassLiftTensorProgram.entry]

def term {degree : ℕ} (security bits : ℕ) (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult)
    (source : Vector (Fin (colors security)) degree) : RationalResult :=
  let input := profile source
  let kernel := BinaryFiniteProduct.current degree (column security bits source output)
  let result := RationalBits.multiply input.data kernel.data
  ⟨result.data, input.work+kernel.work+result.work+3⟩

theorem term_value {degree : ℕ} (security bits : ℕ) (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult)
    (source : Vector (Fin (colors security)) degree) :
    (term security bits output profile source).data.decode =
      (profile source).data.decode *
        ∏ slot, RationalMassLiftTensorProgram.entry security bits (source.get slot).val (output.get slot).val := by
  simp only [term, RationalBits.multiply_value, BinaryFiniteProduct.current_value, column_value]

def current (security bits degree : ℕ) (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryTupleSum.current modulus.count degree (term security bits output profile)
  ⟨result.data, modulus.work+result.work+2⟩

theorem current_value (security bits degree : ℕ) (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult)
    (value : (Fin degree → ℕ) → ℚ)
    (hprofile : ∀ word, (profile word).data.decode = value (fun slot => (word.get slot).val)) :
    (current security bits degree output profile).data.decode =
      RationalMassLiftTensorProgram.current security bits degree value (fun slot => (output.get slot).val) := by
  change (BinaryTupleSum.current _ _ _).data.decode = _
  rw [BinaryTupleSum.current_value]
  unfold RationalMassLiftTensorProgram.current
  apply Finset.sum_congr rfl
  intro source _
  simp only [term_value, hprofile, Vector.get_ofFn]

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

noncomputable def columnWorkPolynomial (degree : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (6*degree+9)+BinaryMassLiftColumn.workPolynomial precision
noncomputable def termHeightPolynomial (degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  inputBits+Polynomial.C degree*BinaryMassLiftColumn.heightPolynomial precision
noncomputable def termWorkPolynomial (degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  inputWork+BinaryFiniteProduct.workPolynomial degree (BinaryMassLiftColumn.heightPolynomial precision)
    (columnWorkPolynomial degree precision)+primitiveWorkPolynomial (termHeightPolynomial degree precision inputBits)+3
noncomputable def heightPolynomial (degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryTupleSum.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial degree (termHeightPolynomial degree precision inputBits)
noncomputable def workPolynomial (degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    BinaryTupleSum.workPolynomial BinaryFirstInverseProgram.colorsPolynomial degree
      (termHeightPolynomial degree precision inputBits) (termWorkPolynomial degree precision inputBits inputWork)+2

theorem column_bounds {degree : ℕ} (security : ℕ) (precision : Polynomial ℕ)
    (source output : Vector (Fin (colors security)) degree) (slot : Fin degree) :
    HeightBound (column security (precision.eval security) source output slot).data.decode
      ((BinaryMassLiftColumn.heightPolynomial precision).eval security) ∧
      (column security (precision.eval security) source output slot).work ≤ (columnWorkPolynomial degree precision).eval security := by
  have h := BinaryMassLiftColumn.current_bounds security precision
    (readVector (first security) source slot).value (readVector (first security) output slot).value
  constructor
  · exact h.1
  · have wi := readVector_work (first security) source slot
    have wo := readVector_work (first security) output slot
    change _+_+_+3 ≤ _
    simp only [columnWorkPolynomial, Polynomial.eval_add, Polynomial.eval_C]
    omega

theorem term_bounds {degree : ℕ} (security : ℕ) (precision inputBits inputWork : Polynomial ℕ)
    (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult)
    (hh : ∀ source, HeightBound (profile source).data.decode (inputBits.eval security))
    (hw : ∀ source, (profile source).work ≤ inputWork.eval security)
    (source : Vector (Fin (colors security)) degree) :
    HeightBound (term security (precision.eval security) output profile source).data.decode
      ((termHeightPolynomial degree precision inputBits).eval security) ∧
      (term security (precision.eval security) output profile source).work ≤
        (termWorkPolynomial degree precision inputBits inputWork).eval security := by
  let H := (termHeightPolynomial degree precision inputBits).eval security
  have hk := BinaryFiniteProduct.current_height degree ((BinaryMassLiftColumn.heightPolynomial precision).eval security)
    (column security (precision.eval security) source output) (fun slot => (column_bounds security precision source output slot).1)
  have wk := BinaryFiniteProduct.current_work degree ((BinaryMassLiftColumn.heightPolynomial precision).eval security)
    ((columnWorkPolynomial degree precision).eval security) (column security (precision.eval security) source output)
    (fun slot => (column_bounds security precision source output slot).1) (fun slot => (column_bounds security precision source output slot).2)
  have hH : H = inputBits.eval security+degree*(BinaryMassLiftColumn.heightPolynomial precision).eval security := by
    simp only [H, termHeightPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have wm := RationalBits.multiply_work (profile source).data
    (BinaryFiniteProduct.current degree (column security (precision.eval security) source output)).data H
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
      ((BinaryMassLiftColumn.heightPolynomial precision).eval security) ((columnWorkPolynomial degree precision).eval security)+primitiveWorkBound H+3
    omega

theorem current_bounds (security degree : ℕ) (precision inputBits inputWork : Polynomial ℕ)
    (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult)
    (hh : ∀ source, HeightBound (profile source).data.decode (inputBits.eval security))
    (hw : ∀ source, (profile source).work ≤ inputWork.eval security) :
    HeightBound (current security (precision.eval security) degree output profile).data.decode
      ((heightPolynomial degree precision inputBits).eval security) ∧
      (current security (precision.eval security) degree output profile).work ≤
        (workPolynomial degree precision inputBits inputWork).eval security := by
  have h := BinaryTupleSum.current_bounds (colors security) degree
    (term security (precision.eval security) output profile)
    ((termHeightPolynomial degree precision inputBits).eval security)
    ((termWorkPolynomial degree precision inputBits inputWork).eval security)
    (fun source => (term_bounds security precision inputBits inputWork output profile hh hw source).1)
    (fun source => (term_bounds security precision inputBits inputWork output profile hh hw source).2)
  have hq := BinaryFirstInverseProgram.colors_bound security
  constructor
  · change HeightBound (BinaryTupleSum.current _ _ _).data.decode _
    apply h.1.mono
    rw [heightPolynomial, BinaryTupleSum.heightPolynomial_eval]
    exact tupleHeight_mono hq (le_refl _)
  · have wq := PublicParameterProgram.modulus_work security
    have wk := h.2.trans (tupleWork_mono hq (le_refl _) (le_refl _))
    change (PublicParameterProgram.modulus security).work+
      (BinaryTupleSum.current (colors security) degree (term security (precision.eval security) output profile)).work+2 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat,
      PublicParameterProgram.workPolynomial_eval, BinaryTupleSum.workPolynomial_eval]
    omega

end
end CurrentAFT.BinaryMassLiftTensor

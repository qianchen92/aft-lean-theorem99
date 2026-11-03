import CurrentAFT.BinaryFirstInverseResources

/-! # Binary primary conjugation before the actual mass lift -/
namespace CurrentAFT.BinaryDensityInverseProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryFirstInverseProgram.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term {count : ℕ} (primary score : Vector RationalBits count) (color : Fin count) : RationalResult :=
  let atom := readVector zero primary color
  let point := readVector zero score color
  let result := RationalBits.multiply atom.value point.value
  ⟨result.data, atom.work+point.work+result.work+3⟩

theorem term_value {count : ℕ} (primary score : Vector RationalBits count) (color : Fin count) :
    (term primary score color).data.decode = (primary.get color).decode*(score.get color).decode := by
  simp only [term, RationalBits.multiply_value, readVector_value]

def conjugate (security bits : ℕ) (score : Vector RationalBits (colors security)) : ArrayResult (colors security) :=
  let reference := BinaryReferenceTables.current security bits
  let result := buildArray (colors security) (term reference.primary score)
  ⟨result.data, reference.work+result.work+2⟩

theorem conjugate_value (security bits : ℕ) (score : Vector RationalBits (colors security)) (output : Fin (colors security)) :
    ((conjugate security bits score).data.get output).decode =
      RationalProposalProgram.primary security bits output.val*(score.get output).decode := by
  simp only [conjugate, buildArray_get, term_value, BinaryReferenceTables.primary_value]

theorem conjugate_inputAt (security bits : ℕ) (score : Vector RationalBits (colors security)) :
    BinaryFirstInverseProgram.inputAt security (conjugate security bits score).data =
      fun output => RationalProposalProgram.primary security bits output*BinaryFirstInverseProgram.inputAt security score output := by
  funext output
  by_cases h : output<colors security
  · simp only [BinaryFirstInverseProgram.inputAt, dif_pos h]
    exact conjugate_value security bits score ⟨output,h⟩
  · simp only [BinaryFirstInverseProgram.inputAt, dif_neg h, mul_zero]

def current (security bits : ℕ) (score : Vector RationalBits (colors security)) (output : Fin (colors security)) : RationalResult :=
  let input := conjugate security bits score
  let result := BinaryFirstInverseProgram.current security bits input.data output
  ⟨result.data, input.work+result.work+3⟩

theorem current_value (security bits : ℕ) (score : Vector RationalBits (colors security)) (output : Fin (colors security)) :
    (current security bits score output).data.decode =
      RationalDensityInverseProgram.current security bits (BinaryFirstInverseProgram.inputAt security score) output.val := by
  change (BinaryFirstInverseProgram.current _ _ _ _).data.decode = _
  rw [BinaryFirstInverseProgram.current_value, conjugate_inputAt]
  rfl

noncomputable section
open scoped Classical

noncomputable def operandHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.heightPolynomial precision+inputBits
noncomputable def conjugateHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*operandHeightPolynomial precision inputBits
noncomputable def conjugateWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  BinaryReferenceTables.currentWorkPolynomial precision+Q*(6*Q+11+
    primitiveWorkPolynomial (operandHeightPolynomial precision inputBits))+4

theorem conjugate_bounds (security : ℕ) (precision inputBits : Polynomial ℕ)
    (score : Vector RationalBits (colors security))
    (hs : ∀ color, HeightBound (score.get color).decode (inputBits.eval security)) :
    (∀ color, HeightBound ((conjugate security (precision.eval security) score).data.get color).decode
      ((conjugateHeightPolynomial precision inputBits).eval security)) ∧
      (conjugate security (precision.eval security) score).work ≤
        (conjugateWorkPolynomial precision inputBits).eval security := by
  let reference := BinaryReferenceTables.current security (precision.eval security)
  let H := (operandHeightPolynomial precision inputBits).eval security
  let Q := BinaryFirstInverseProgram.colorsPolynomial.eval security
  have hq : colors security ≤ Q := BinaryFirstInverseProgram.colors_bound security
  have hr := BinaryReferenceTables.current_bounds security precision
  have br : (BinaryReferenceTables.heightPolynomial precision).eval security ≤ H := by
    simp only [H, operandHeightPolynomial, Polynomial.eval_add]; omega
  have bs : inputBits.eval security ≤ H := by
    simp only [H, operandHeightPolynomial, Polynomial.eval_add]; omega
  have hp (color : Fin (colors security)) : HeightBound (reference.primary.get color).decode H := (hr.1 color).mono br
  have hf (color : Fin (colors security)) : HeightBound (score.get color).decode H := (hs color).mono bs
  have ht (color : Fin (colors security)) : HeightBound (term reference.primary score color).data.decode (2*H) := by
    rw [term_value]
    exact ((hp color).mul (hf color)).mono (by omega)
  have wt (color : Fin (colors security)) :
      (term reference.primary score color).work ≤ 6*Q+9+primitiveWorkBound H := by
    have wp := readVector_work zero reference.primary color
    have ws := readVector_work zero score color
    change (readVector zero reference.primary color).work ≤ 3*colors security+3 at wp
    change (readVector zero score color).work ≤ 3*colors security+3 at ws
    have wm := RationalBits.multiply_work (readVector zero reference.primary color).value (readVector zero score color).value H
      (by rw [readVector_value]; exact hp color) (by rw [readVector_value]; exact hf color)
    change _+_+_+3 ≤ _
    omega
  constructor
  · intro color
    change HeightBound ((buildArray _ _).data.get color).decode _
    rw [buildArray_get]
    simpa only [conjugateHeightPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat] using ht color
  · have wa := (buildArray_work (colors security) (6*Q+9+primitiveWorkBound H) (term reference.primary score) wt).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hq) 2)
    have wref : reference.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
    change reference.work+(buildArray (colors security) (term reference.primary score)).work+2 ≤ _
    simp only [conjugateWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      primitiveWorkPolynomial_eval]
    change _ ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security+Q*(6*Q+11+primitiveWorkBound H)+4
    have hid : Q*(6*Q+9+primitiveWorkBound H+2)+2 = Q*(6*Q+11+primitiveWorkBound H)+2 := by ring
    rw [hid] at wa
    omega

noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.currentHeightPolynomial precision (conjugateHeightPolynomial precision inputBits)
noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  conjugateWorkPolynomial precision inputBits+
    BinaryFirstInverseProgram.currentWorkPolynomial precision (conjugateHeightPolynomial precision inputBits)+3

theorem current_bounds (security : ℕ) (precision inputBits : Polynomial ℕ)
    (score : Vector RationalBits (colors security)) (output : Fin (colors security))
    (hs : ∀ color, HeightBound (score.get color).decode (inputBits.eval security)) :
    HeightBound (current security (precision.eval security) score output).data.decode
      ((currentHeightPolynomial precision inputBits).eval security) ∧
      (current security (precision.eval security) score output).work ≤
        (currentWorkPolynomial precision inputBits).eval security := by
  have hc := conjugate_bounds security precision inputBits score hs
  have hi := BinaryFirstInverseProgram.current_bounds security precision (conjugateHeightPolynomial precision inputBits)
    (conjugate security (precision.eval security) score).data output hc.1
  constructor
  · exact hi.1
  · change _+_+3 ≤ _
    simp only [currentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
    omega

end
end CurrentAFT.BinaryDensityInverseProgram

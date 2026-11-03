import CurrentAFT.BinaryCoefficientAtomFormula
import CurrentAFT.BinaryReferenceTables
import CurrentAFT.BinaryMassLiftColumn
import CurrentAFT.RationalCoefficientExtraction

/-! Actual uniform-centering atoms, with computed prime and reference cache. -/
namespace CurrentAFT.BinaryCoefficientAtom
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (source output : Fin (colors security)) : RationalResult :=
  let metadata := BinaryProposalMetadata.current security
  let reference := BinaryReferenceTables.current security bits
  let primary := readVector zero reference.primary output
  let point := BinaryMassLiftColumn.point source output
  let result := BinaryCoefficientAtomFormula.current point.data metadata.colors primary.value
  ⟨result.data,metadata.work+reference.work+primary.work+point.work+result.work+5⟩

theorem current_value (security bits : ℕ) (source output : Fin (colors security)) :
    (current security bits source output).data.decode = RationalCoefficientExtraction.atom security bits source.val output.val := by
  simp only [current, BinaryCoefficientAtomFormula.current_value, BinaryMassLiftColumn.point_value,
    readVector_value, BinaryReferenceTables.primary_value, (BinaryProposalMetadata.current_value security).1,
    RationalCoefficientExtraction.atom, PublicParameterProgram.modulus_value, Fin.ext_iff, eq_comm]

noncomputable section
noncomputable def operandPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.sizePolynomial+BinaryReferenceTables.heightPolynomial precision+1
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientAtomFormula.heightPolynomial (operandPolynomial precision)
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.currentWorkPolynomial+BinaryReferenceTables.currentWorkPolynomial precision+
    15*BinaryFirstInverseProgram.colorsPolynomial+15+BinaryCoefficientAtomFormula.workPolynomial (operandPolynomial precision)

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ) (source output : Fin (colors security)) :
    HeightBound (current security (precision.eval security) source output).data.decode ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) source output).work ≤ (workPolynomial precision).eval security := by
  let H := (operandPolynomial precision).eval security
  have hh := BinaryReferenceTables.current_bounds security precision
  have hp : HeightBound (BinaryMassLiftColumn.point source output).data.decode H :=
    (BinaryMassLiftColumn.point_height source output).mono (by simp only [H, operandPolynomial, Polynomial.eval_add, Polynomial.eval_one]; omega)
  have hq : HeightBound (BinaryProposalMetadata.current security).colors.decode H :=
    (BinaryProposalMetadata.current_height security).1.mono (by simp only [H, operandPolynomial, Polynomial.eval_add,
      Polynomial.eval_one, BinaryProposalMetadata.sizePolynomial_eval]; omega)
  have hr : HeightBound (readVector zero (BinaryReferenceTables.current security (precision.eval security)).primary output).value.decode H := by
    rw [readVector_value]
    exact (hh.1 output).mono (by simp only [H, operandPolynomial, Polynomial.eval_add, Polynomial.eval_one]; omega)
  have hf := BinaryCoefficientAtomFormula.current_bounds _ _ _ H hp hq hr
  constructor
  · simpa only [heightPolynomial, BinaryCoefficientAtomFormula.heightPolynomial_eval] using hf.1
  · have wm := BinaryProposalMetadata.current_work security
    have wr := hh.2.2.2.2
    have wp := readVector_work zero (BinaryReferenceTables.current security (precision.eval security)).primary output
    have wd := BinaryMassLiftColumn.point_work source output
    have hc := BinaryFirstInverseProgram.colors_bound security
    change colors security ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security at hc
    change (readVector zero (BinaryReferenceTables.current security (precision.eval security)).primary output).work ≤ 3*colors security+3 at wp
    change _+_+_+_+_+5 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      BinaryProposalMetadata.currentWorkPolynomial_eval, BinaryCoefficientAtomFormula.workPolynomial_eval]
    dsimp only [H] at hf
    omega

end
end CurrentAFT.BinaryCoefficientAtom

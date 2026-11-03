import CurrentAFT.BinaryPrimaryFixedMass
import CurrentAFT.BinaryPrimaryCenteredScore
import CurrentAFT.BinaryScalarAverage

/-! Actual centered primary four-endpoint mass with its single shared scalar. -/
namespace CurrentAFT.BinaryPrimaryMass
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (compensator attachment : IntegerBits) (source : Fin (colors security))
    (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let score := BinaryPrimaryCenteredScore.current security bits source
  let result := BinaryScalarAverage.current security bits (fun scalar =>
    BinaryPrimaryFixedMass.fixedMass security bits compensator attachment scalar score.data word)
  ⟨result.data,score.work+result.work+2⟩

theorem current_value (security bits : ℕ) (compensator attachment : IntegerBits) (source : Fin (colors security))
    (word : Vector (Fin (colors security)) 4) :
    (current security bits compensator attachment source word).data.decode=
      RationalRootMassProgram.primaryMass security bits compensator.decode attachment.decode
        (RationalPrimaryColumnProgram.centerDelta security bits source.val) (fun index => (word.get index).val) := by
  unfold current
  rw [BinaryScalarAverage.current_value security bits _ (fun scalar =>
    RationalRootMassProgram.fixedMass security bits compensator.decode attachment.decode scalar
      (RationalPrimaryColumnProgram.centerDelta security bits source.val) (fun index => (word.get index).val))]
  · rfl
  · intro scalar
    exact BinaryPrimaryFixedMass.fixedMass_value_of security bits compensator attachment scalar
      (BinaryPrimaryCenteredScore.current security bits source).data
      (RationalPrimaryColumnProgram.centerDelta security bits source.val)
      (BinaryPrimaryCenteredScore.current_value security bits source) word

noncomputable section
noncomputable def jointBits (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  inputBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial
noncomputable def fixedHeight (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFixedMass.heightPolynomial precision (jointBits inputBits) (BinaryPrimaryCenteredScore.heightPolynomial precision)
noncomputable def fixedWork (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFixedMass.workPolynomial precision (jointBits inputBits) (BinaryPrimaryCenteredScore.heightPolynomial precision)
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.heightPolynomial precision (fixedHeight precision inputBits)
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryCenteredScore.workPolynomial precision+
    BinaryCoefficientScalarAverage.workPolynomial precision (fixedHeight precision inputBits) (fixedWork precision inputBits)+2

theorem current_bounds (security : ℕ) (precision inputBits : Polynomial ℕ) (compensator attachment : IntegerBits)
    (source : Fin (colors security)) (word : Vector (Fin (colors security)) 4)
    (hc : compensator.digits.length ≤ inputBits.eval security) (ha : attachment.digits.length ≤ inputBits.eval security) :
    HeightBound (current security (precision.eval security) compensator attachment source word).data.decode
      ((heightPolynomial precision inputBits).eval security) ∧
      (current security (precision.eval security) compensator attachment source word).work ≤
        (workPolynomial precision inputBits).eval security := by
  have hscore := BinaryPrimaryCenteredScore.current_bounds security precision source
  have hf (scalar : IntegerBits) (hs : scalar.digits.length ≤ BinaryCoefficientScalarAverage.scalarBitsPolynomial.eval security) :=
    BinaryPrimaryFixedMass.fixedMass_bounds security precision (jointBits inputBits) (BinaryPrimaryCenteredScore.heightPolynomial precision)
      compensator attachment scalar (BinaryPrimaryCenteredScore.current security (precision.eval security) source).data word
      (hc.trans (by simp only [jointBits,Polynomial.eval_add]; omega))
      (ha.trans (by simp only [jointBits,Polynomial.eval_add]; omega))
      (hs.trans (by simp only [jointBits,Polynomial.eval_add]; omega)) hscore.1
  have havg := BinaryScalarAverage.current_bounds security precision (fixedHeight precision inputBits) (fixedWork precision inputBits)
    (fun scalar => BinaryPrimaryFixedMass.fixedMass security (precision.eval security) compensator attachment scalar
      (BinaryPrimaryCenteredScore.current security (precision.eval security) source).data word) hf
  refine ⟨havg.1,?_⟩
  change _+_+2 ≤ _
  simpa only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat] using
    Nat.add_le_add_right (Nat.add_le_add hscore.2 havg.2) 2

end
end CurrentAFT.BinaryPrimaryMass

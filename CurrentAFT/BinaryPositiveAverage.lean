import CurrentAFT.BinaryPositiveReference
import CurrentAFT.BinarySeedRootAverage
import CurrentAFT.BinaryScalarAverage

/-! The positive four-endpoint reference averages its two independent roots
inside the single actual scalar average. -/
namespace CurrentAFT.BinaryPositiveAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (word : Vector (Fin (colors security)) 4) : RationalResult :=
  BinaryScalarAverage.current security bits (fun scalar =>
    BinarySeedRootAverage.current security bits (fun compensator =>
      BinarySeedRootAverage.current security bits (fun attachment =>
        BinaryPositiveReference.fixedMass security bits compensator attachment scalar word)))

theorem current_value (security bits : ℕ) (word : Vector (Fin (colors security)) 4) :
    (current security bits word).data.decode =
      RationalPositiveReferenceProgram.current security bits (fun index => (word.get index).val) := by
  unfold current
  rw [BinaryScalarAverage.current_value security bits _
    (fun scalar => RationalProposalProgram.seedEvaluate security bits (fun compensator =>
      RationalProposalProgram.seedEvaluate security bits (fun attachment =>
        RationalPositiveReferenceProgram.fixedMass security bits (DiffuseProfiles.actualBlur security compensator)
          (DiffuseProfiles.actualBlur security attachment) scalar (fun index => (word.get index).val))))]
  · rfl
  · intro scalar
    apply BinarySeedRootAverage.current_value security bits _ (fun compensator =>
      RationalProposalProgram.seedEvaluate security bits (fun attachment =>
        RationalPositiveReferenceProgram.fixedMass security bits compensator (DiffuseProfiles.actualBlur security attachment)
          scalar.decode (fun index => (word.get index).val)))
    intro compensator
    apply BinarySeedRootAverage.current_value security bits _ (fun attachment =>
      RationalPositiveReferenceProgram.fixedMass security bits compensator.decode attachment scalar.decode
        (fun index => (word.get index).val))
    intro attachment
    exact BinaryPositiveReference.fixedMass_value security bits compensator attachment scalar word

noncomputable section
noncomputable def inputBits : Polynomial ℕ := BinarySeedRootAverage.rootBitsPolynomial+BinaryCoefficientScalarAverage.scalarBitsPolynomial
noncomputable def innerHeight (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySeedRootAverage.heightPolynomial precision (BinaryPositiveReference.heightPolynomial precision inputBits)
noncomputable def innerWork (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySeedRootAverage.workPolynomial precision (BinaryPositiveReference.heightPolynomial precision inputBits)
    (BinaryPositiveReference.workPolynomial precision inputBits)
noncomputable def outerHeight (precision : Polynomial ℕ) : Polynomial ℕ := BinarySeedRootAverage.heightPolynomial precision (innerHeight precision)
noncomputable def outerWork (precision : Polynomial ℕ) : Polynomial ℕ := BinarySeedRootAverage.workPolynomial precision (innerHeight precision) (innerWork precision)
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryCoefficientScalarAverage.heightPolynomial precision (outerHeight precision)
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryCoefficientScalarAverage.workPolynomial precision (outerHeight precision) (outerWork precision)

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ) (word : Vector (Fin (colors security)) 4) :
    HeightBound (current security (precision.eval security) word).data.decode ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) word).work ≤ (workPolynomial precision).eval security := by
  apply BinaryScalarAverage.current_bounds
  intro scalar hs
  apply BinarySeedRootAverage.current_bounds
  intro compensator hc
  apply BinarySeedRootAverage.current_bounds
  intro attachment ha
  apply BinaryPositiveReference.fixedMass_bounds security precision inputBits compensator attachment scalar word
  · exact hc.trans (by simp only [inputBits, Polynomial.eval_add]; omega)
  · exact ha.trans (by simp only [inputBits, Polynomial.eval_add]; omega)
  · exact hs.trans (by simp only [inputBits, Polynomial.eval_add]; omega)

end
end CurrentAFT.BinaryPositiveAverage

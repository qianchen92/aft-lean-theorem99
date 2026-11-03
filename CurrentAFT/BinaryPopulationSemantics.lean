import CurrentAFT.BinaryFamilyBinomial
import CurrentAFT.BinaryFamilyValidSemantics

/-! # Palette-valid semantics for the executed truncated population power -/
namespace CurrentAFT.BinaryPopulationSemantics
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem binomial_value (order population base : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (table : CoefficientProgram order) (actual : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ arity inputs centers, (∀ i, inputs.get i<base) → (∀ i, centers.get i<base) →
      (table arity inputs centers).value.decode=actual arity inputs.get centers.get)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<base) (hb : ∀ i, centers.get i<base) :
    (BinaryFamilyBinomial.current order population programs table arity inputs centers).value.decode=
      RationalFamilyProductProgram.binomial order population actual arity inputs.get centers.get := by
  simp only [BinaryFamilyBinomial.current,sumFin_value,BinaryFamilyBinomial.term,RationalBits.multiply_value,
    BinaryBinomialCoefficient.current_value,
    BinaryFamilyValidSemantics.power_value order base programs hcorrect hcomplete table actual hvalue _ arity inputs centers hi hb]
  exact Fin.sum_univ_eq_sum_range (fun count => (population.choose count:ℚ)*
    RationalFamilyProductProgram.power order actual count arity inputs.get centers.get) (order+1)

end
end CurrentAFT.BinaryPopulationSemantics

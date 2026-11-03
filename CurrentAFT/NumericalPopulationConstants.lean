import CurrentAFT.NumericalLocalConstants
import CurrentAFT.RationalBackgroundPopulationProgram

/-! # Polynomial errors for the literal fixed-queue three-population program -/
namespace CurrentAFT.NumericalPopulationConstants
open AFT PolynomialErrorEnvelope
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize

local macro "finish_population_envelope" : tactic => `(tactic|
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow)

theorem free_population : PolynomialErrorEnvelope (fun security => (BackgroundPopulationBounds.freeCount security:ℝ)) := by
  apply PolynomialErrorEnvelope.body.mono
  intro security
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (show BackgroundPopulationBounds.freeCount security≤Parameters.bodySize security by
    unfold BackgroundPopulationBounds.freeCount
    omega)

theorem population_bound (order : ℕ) (population : ℕ→ℕ) (A : ℕ→ℝ)
    (hp : PolynomialErrorEnvelope (fun security => (population security:ℝ)))
    (hA : PolynomialErrorEnvelope A) :
    PolynomialErrorEnvelope (fun security => RationalPopulationApproximation.bound order (population security) (A security)) := by
  simp only [RationalPopulationApproximation.bound, RationalFamilyProductProgram.growth, Nat.cast_add, Nat.cast_one]
  finish_population_envelope

theorem population_error (order : ℕ) (population : ℕ→ℕ) (A e : ℕ→ℝ)
    (hp : PolynomialErrorEnvelope (fun security => (population security:ℝ)))
    (hA : PolynomialErrorEnvelope A) (he : PolynomialErrorEnvelope e) :
    PolynomialErrorEnvelope (fun security => RationalPopulationApproximation.error order (population security) (A security) (e security)) := by
  simp only [RationalPopulationApproximation.error, RationalFamilyProductProgram.growth, Nat.cast_add, Nat.cast_one]
  finish_population_envelope

theorem free_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.freeBound security order) := by
  apply population_bound order _ _ free_population
  have hc := NumericalLocalConstants.coordinate_factor order
  simp only [RationalMarkedPairProgram.freeBound]
  finish_population_envelope

theorem queue_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.queueBound security order) :=
  population_bound order _ _ PolynomialErrorEnvelope.modulus (NumericalLocalConstants.translation_bound order)

theorem leg_atom_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.legAtomBound security order) := by
  have hc := NumericalLocalConstants.coordinate_factor order
  simp only [RationalBackgroundPopulationProgram.legAtomBound]
  finish_population_envelope

theorem leg_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.legBound security order) :=
  population_bound order _ _ PolynomialErrorEnvelope.legs (leg_atom_bound order)

theorem free_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.freeError security order) := by
  apply population_error order _ _ _ free_population _ NumericalLocalConstants.free_error
  have hc := NumericalLocalConstants.coordinate_factor order
  simp only [RationalMarkedPairProgram.freeBound]
  finish_population_envelope

theorem queue_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.queueError security order) :=
  population_error order _ _ _ PolynomialErrorEnvelope.modulus (NumericalLocalConstants.translation_bound order)
    NumericalLocalConstants.translation_error

theorem leg_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.legError security order) :=
  population_error order _ _ _ PolynomialErrorEnvelope.legs (leg_atom_bound order) (NumericalLocalConstants.complete_leg order)

theorem complete (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.errorConstant security order) := by
  have hfB := free_bound order
  have hqB := queue_bound order
  have hlB := leg_bound order
  have hfE := free_error order
  have hqE := queue_error order
  have hlE := leg_error order
  simp only [RationalBackgroundPopulationProgram.errorConstant, RationalBackgroundPopulationProgram.freeQueueBound,
    RationalBackgroundPopulationProgram.freeQueueError, RationalActualFamilyApproximation.productError]
  finish_population_envelope

theorem complete_negligible (order : ℕ) : Negligible (fun security =>
    RationalBackgroundPopulationProgram.errorConstant security order*(1/(2:ℝ)^security)) :=
  (complete order).dyadic

end
end CurrentAFT.NumericalPopulationConstants

import CurrentAFT.CompleteRaisingStability
import CurrentAFT.CompleteRaisingEvaluation
import CurrentAFT.BackgroundPolynomialEvaluation
import CurrentAFT.PhysicalSynthesis

/-!
# Constructed calibration for the independent-root reference experiment

This is the actual reference solve used before adding the cycle-root
perturbation. Its coefficients, physical image, and public weight are
defined explicitly. The result makes no claim about the dependent cycle.
-/
namespace CurrentAFT.IndependentCalibration
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse
  LocalCoefficientFamily BackgroundRates BackgroundFamilies BackgroundEvaluation
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference

def solution (security order : ℕ) (horder : 2 ≤ order) : Family security order :=
  CompleteRaisingInverse.inverse security order (by omega)
    (ActualBackgroundInverse.inverse security order horder)

theorem response_solution (security order : ℕ) (horder : 2 ≤ order) :
    solution security order horder + CompleteRaising.raisingLinear security order (by omega)
      (solution security order horder) = ActualBackgroundInverse.inverse security order horder :=
  CompleteRaisingInverse.response_inverse security order (by omega) _

theorem solution_constant (security order : ℕ) (horder : 2 ≤ order) :
    solution security order horder (zeroArity order) = (1 : Family security order) (zeroArity order) := by
  rw [solution, CompleteRaisingStability.inverse_constant, ActualBackgroundInverse.inverse_unit_constant]

/-- The actual normalized local responses cancel the complete independent
background PGF through the requested total degree. -/
theorem physical_image (security order : ℕ) (horder : 2 ≤ order) :
    evaluation security order
      (CompleteRaisingEvaluation.normalizedResponse security order (by omega) (solution security order horder)) *
      TruncatedOutput.quotientMap order
        (BackgroundPolynomialEvaluation.finiteGenerating
          (BackgroundPolynomialEvaluation.backgroundLaw security)
          (BackgroundPolynomialEvaluation.endpointFactor security)) = 1 := by
  rw [CompleteRaisingEvaluation.normalizedResponse_image, response_solution]
  exact BackgroundPolynomialEvaluation.inverse_physical_background security order horder

def norm (security order : ℕ) (family : Family security order) : ℝ :=
  familyNorm (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) family

theorem solution_bounds_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      norm security order (solution security order horder) ≤ 4 ∧
      norm security order (solution security order horder - 1) ≤
        4 * RaisingPatternNorm.stabilityConstant order / (Parameters.base security : ℝ) ^ 38 +
          2 * ActualBackground.stabilityConstant order / (Parameters.base security : ℝ) ^ 6 := by
  filter_upwards [CompleteRaisingStability.inverse_bounds_eventually order (by omega),
    ActualBackgroundInverse.inverse_bounds_eventually order horder] with security hraising hbackground
  have h := hraising (ActualBackgroundInverse.inverse security order horder)
  have hb := FirstResponse.base_pos security
  have hc := CompleteRaisingStability.stabilityConstant_nonneg order
  constructor
  · exact h.1.trans ((mul_le_mul_of_nonneg_left hbackground.1 (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num))
  · have hsplit : solution security order horder - 1 =
        (solution security order horder - ActualBackgroundInverse.inverse security order horder) +
          (ActualBackgroundInverse.inverse security order horder - 1) := by abel
    rw [hsplit]
    apply (familyNorm_add_le _ _ order _ _ (RaisingPatternBudget.primaryFactor_pos security).le
      (RaisingPatternBudget.bodyFactor_pos security).le _ _).trans
    apply add_le_add _ hbackground.2
    apply h.2.trans
    exact (mul_le_mul_of_nonneg_left hbackground.1
      (div_nonneg (mul_nonneg (by norm_num) hc) (pow_nonneg hb.le _))).trans_eq (by ring)

def coefficients (security order : ℕ) (horder : 2 ≤ order) : Coefficients security order :=
  familyCoefficientEquiv (primaryLaw security) (bodyReference security) order (solution security order horder)

theorem coefficients_scalar (security order : ℕ) (horder : 2 ≤ order) :
    (coefficients security order horder).1 = 1 := by
  change scalarAt (primaryLaw security) (bodyReference security) (solution security order horder (zeroArity order)) = 1
  rw [solution_constant]
  exact map_one (Augmentation.scalarHom (primaryLaw security) (bodyReference security) order)

/-- The reference-calibrated coefficient family gives a genuine public
signed weight of mass one under the same two independent control pools. -/
theorem public_weight_mass_one (security order primaryPool bodyPool : ℕ) (horder : 2 ≤ order) :
    kernelMean (PhysicalSynthesis.groupLaw security) (bodyReference security)
      (PhysicalSynthesis.coefficientWeight security order primaryPool bodyPool (coefficients security order horder)) = 1 :=
  PhysicalSynthesis.coefficientWeight_mass_one security order primaryPool bodyPool _
    (coefficients_scalar security order horder)

end
end CurrentAFT.IndependentCalibration

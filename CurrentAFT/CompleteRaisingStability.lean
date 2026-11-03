import CurrentAFT.CompleteRaisingPatternIdentity
import CurrentAFT.RaisingPatternNorm
import CurrentAFT.RaisingInverseGeometry

/-!
# Stability of the actual complete independent-root raising response

The exact finite-source product identity identifies the original two-role
raising map with its Hilbert arity-pattern assembly. All local operator
bounds, tensor contractions, and pattern counts have already been proved
for the current public parameters. The resulting bound is uniform over
every joint canonical input. Its explicit finite inverse preserves the
constant fiber and is bounded after one fixed-order threshold.
-/
namespace CurrentAFT.CompleteRaisingStability

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse
  LocalCoefficientFamily LocalRaisingBounds RaisingPatternBudget RaisingPatternNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

theorem homogeneous_eq_patterns (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    CompleteRaising.homogeneousCorrectionLinear security order horder r s kernel =
      RaisingPatternNorm.homogeneousCorrection security order horder r s kernel := by
  simp only [CompleteRaising.homogeneousCorrectionLinear, LinearMap.sum_apply]
  unfold RaisingPatternNorm.homogeneousCorrection RaisingPatternNorm.patternCorrection
  apply Finset.sum_congr rfl
  intro selected _
  exact CompleteRaisingPatternIdentity.selectedCorrection_eq_sum_patterns security order horder selected kernel

theorem raising_eq_patterns (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) :
    CompleteRaising.raisingLinear security order horder family = assembledRaising security order horder family := by
  change (∑ arity : TruncatedArity order,
    CompleteRaising.homogeneousCorrectionLinear security order horder arity.val.1.val arity.val.2.val (family arity)) = _
  unfold assembledRaising
  exact Finset.sum_congr rfl (fun arity _ => homogeneous_eq_patterns security order horder _ _ (family arity))

/-- The actual complete raising map satisfies a current-parameter bound;
no stability estimate or factorization of the input kernel is a premise. -/
theorem raising_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (CompleteRaising.raisingLinear security order horder family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ) ^ 38) *
          LocalRaisingBounds.coefficientNorm security order family := by
  filter_upwards [assembledRaising_norm_eventually order horder] with security hbound family
  rw [raising_eq_patterns]
  exact hbound family

theorem stabilityConstant_nonneg (order : ℕ) : 0 ≤ stabilityConstant order :=
  mul_nonneg (degreeConstant_nonneg order) (add_nonneg raisingConstant_nonneg (by norm_num))

private theorem norm_nonneg (security order : ℕ) (family : Family security order) :
    0 ≤ LocalRaisingBounds.coefficientNorm security order family :=
  familyNorm_nonneg _ _ order _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le family

theorem inverse_constant (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) :
    CompleteRaisingInverse.inverse security order horder family (zeroArity order) = family (zeroArity order) := by
  have hraise := CompleteRaising.raisingLinear_raises security order horder 0
    (CompleteRaisingInverse.inverse security order horder family) (vanishesBelow_zero _ _ order _)
  have hzero := hraise (zeroArity order) (by change 0 + 0 < 0 + 1; decide)
  have hequal := congrArg (fun value : Family security order => value (zeroArity order))
    (CompleteRaisingInverse.response_inverse security order horder family)
  change CompleteRaisingInverse.inverse security order horder family (zeroArity order) +
    CompleteRaising.raisingLinear security order horder
      (CompleteRaisingInverse.inverse security order horder family) (zeroArity order) = _ at hequal
  rwa [hzero, add_zero] at hequal

/-- The same actual finite inverse has norm at most two and a decaying
correction, uniformly over all canonical families at this fixed order. -/
theorem inverse_bounds_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (CompleteRaisingInverse.inverse security order horder family) ≤
          2 * LocalRaisingBounds.coefficientNorm security order family ∧
        LocalRaisingBounds.coefficientNorm security order (CompleteRaisingInverse.inverse security order horder family - family) ≤
          (2 * stabilityConstant order / (Parameters.base security : ℝ) ^ 38) *
            LocalRaisingBounds.coefficientNorm security order family := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * stabilityConstant order)
  filter_upwards [eventually_ge_atTop threshold, raising_norm_eventually order horder]
    with security hsecurity hupper family
  let theta := stabilityConstant order / (Parameters.base security : ℝ) ^ 38
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hlarge : 2 * stabilityConstant order ≤ (Parameters.base security : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 38 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 38 by omega)
  have htheta : 0 ≤ theta := div_nonneg (stabilityConstant_nonneg order) (pow_nonneg hb.le _)
  have hhalf : theta ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos hb _)).mpr
    linarith
  have hgap : theta < 1 := by linarith
  have hinverse := RaisingInverseGeometry.finiteInverse_norm security order
    (CompleteRaising.raisingLinear security order horder) theta htheta hgap hupper family
  have hcorrection := RaisingInverseGeometry.finiteInverse_correction security order
    (CompleteRaising.raisingLinear security order horder) theta htheta hgap hupper family
  constructor
  · apply hinverse.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg security order family)
    apply (div_le_iff₀ (sub_pos.mpr hgap)).mpr
    linarith
  · apply hcorrection.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg security order family)
    calc
      _ ≤ theta / (1 / 2) := div_le_div_of_nonneg_left htheta (by norm_num) (by linarith)
      _ = _ := by dsimp only [theta]; ring

end
end CurrentAFT.CompleteRaisingStability

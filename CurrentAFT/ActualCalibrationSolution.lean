import CurrentAFT.ActualCompleteStability

/-! # The actual stable signed calibration solution

The operator is the concrete common-queue response assembled in
`ActualCompleteStability`. The threshold below is chosen from its proved
current-parameter bound. No inverse, response norm, or construction
existence is an assumption of this calibration result. Its physical
polynomial identification is a separate theorem under construction.
-/
namespace CurrentAFT.ActualCompleteStability
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalCoefficientFamily ControlCoordinates
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm Augmentation
  BackgroundRates BackgroundLinear ActualBackground
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance solutionFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference BackgroundRates.ordinaryPool

private theorem hp (security : ℕ) : 0 ≤ primaryFactor security := (RaisingPatternBudget.primaryFactor_pos security).le
private theorem hb (security : ℕ) : 0 ≤ bodyFactor security := (RaisingPatternBudget.bodyFactor_pos security).le

private theorem norm_nonneg (security order : ℕ) (family : Family security order) :
    0 ≤ LocalRaisingBounds.coefficientNorm security order family :=
  familyNorm_nonneg _ _ order _ _ (hp security) (hb security) family

theorem rootCorrection_scalar (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) (family : Family security order) :
    scalarHom (primaryLaw security) (bodyReference security) order (rootCorrection security order horder hroom layout family) = 0 := by
  have hroot (queue : ℤ) : scalarHom (primaryLaw security) (bodyReference security) order
      (ActualRootFamily.rootLinear security order (by omega) hroom queue layout family) = 0 := by
    change scalarAt _ _ ((ActualRootFamily.rootLinear security order (by omega) hroom queue layout family) (zeroArity order)) = 0
    rw [ActualRootFamily.rootLinear_zero_constant]
    rfl
  simp only [rootCorrection, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, map_mul, hroot,
    mul_zero, smul_zero, Finset.sum_const_zero]

theorem independentResponse_scalar (security order : ℕ) (horder : 2 ≤ order) (family : Family security order) :
    scalarHom (primaryLaw security) (bodyReference security) order (independentResponse security order horder family) =
      scalarHom (primaryLaw security) (bodyReference security) order family := by
  have hbackground : scalarHom (primaryLaw security) (bodyReference security) order (background security order horder) = 1 := by
    have h := (zero_fiber_eq_iff_scalar_eq (primaryLaw security) (bodyReference security) order _ _).mp
      (ActualBackgroundInverse.background_unit_constant security order horder)
    simpa only [map_one] using h
  have hraising : scalarHom (primaryLaw security) (bodyReference security) order
      (CompleteRaising.raisingLinear security order (by omega) family) = 0 := by
    have h := CompleteRaising.raisingLinear_raises security order (by omega) 0 family (GradedInverse.vanishesBelow_zero _ _ order family)
    have hz := h (zeroArity order) (by change 0 + 0 < 0 + 1; omega)
    change scalarAt _ _ ((CompleteRaising.raisingLinear security order (by omega) family) (zeroArity order)) = 0
    rw [hz]
    rfl
  change scalarHom _ _ order (background security order horder * (family + _)) = _
  rw [map_mul, map_add, hbackground, hraising, add_zero, one_mul]

theorem fullResponse_scalar (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) (family : Family security order) :
    scalarHom (primaryLaw security) (bodyReference security) order (fullResponse security order horder hroom layout family) =
      scalarHom (primaryLaw security) (bodyReference security) order family := by
  change scalarHom _ _ order (independentResponse security order horder family + rootCorrection security order horder hroom layout family) = _
  rw [map_add, independentResponse_scalar, rootCorrection_scalar, add_zero]

theorem stable_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ hroom : 2 * order ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security,
      stabilityConstant order / (Parameters.base security : ℝ)^6 ≤ 1 / 2 ∧
      ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (family - fullResponse security order horder hroom layout family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * stabilityConstant order)
  filter_upwards [fullResponse_defect_eventually order horder, eventually_ge_atTop threshold]
    with security hdefect hsecurity hroom layout
  refine ⟨?_, hdefect hroom layout⟩
  have hbase : 2 * stabilityConstant order ≤ (Parameters.base security : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr (by unfold Parameters.base; omega))
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ)^6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 6 by omega)
  apply (div_le_iff₀ (pow_pos (FirstResponse.base_pos security) _)).mpr
  linarith

private theorem exists_stable_threshold (order : ℕ) (horder : 2 ≤ order) :
    ∃ threshold : ℕ, ∀ security, threshold ≤ security → ∀ hroom : 2 * order ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security,
      stabilityConstant order / (Parameters.base security : ℝ)^6 ≤ 1 / 2 ∧
      ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (family - fullResponse security order horder hroom layout family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family :=
  Filter.eventually_atTop.mp (stable_eventually order horder)

/-- A public fixed-order threshold obtained from the proved actual bound. -/
def threshold (order : ℕ) (horder : 2 ≤ order) : ℕ :=
  max (2 * order) (Classical.choose (exists_stable_threshold order horder))

def room (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security) : 2 * order ≤ security :=
  (le_max_left _ _).trans hsecurity

theorem stable (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    stabilityConstant order / (Parameters.base security : ℝ)^6 ≤ 1 / 2 ∧
      ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order
        (family - fullResponse security order horder (room security order horder hsecurity) layout family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family :=
  Classical.choose_spec (exists_stable_threshold order horder) security
    ((le_max_right _ _).trans hsecurity) _ layout

theorem calibration_existsUnique (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) (target : Family security order) :
    ∃ coefficient, fullResponse security order horder (room security order horder hsecurity) layout coefficient = target ∧
      (∀ other, fullResponse security order horder (room security order horder hsecurity) layout other = target → other = coefficient) ∧
      ∀ reference, LocalRaisingBounds.coefficientNorm security order (coefficient - reference) ≤
        LocalRaisingBounds.coefficientNorm security order
          (target - fullResponse security order horder (room security order horder hsecurity) layout reference) /
            (1 - stabilityConstant order / (Parameters.base security : ℝ)^6) := by
  have hs := stable security order horder hsecurity layout
  exact family_calibration_existsUnique (primaryLaw security) (bodyReference security) order
    (primaryReference_positive security) (bodyReference_positive security)
    (primaryFactor security) (bodyFactor security) (RaisingPatternBudget.primaryFactor_pos security)
    (RaisingPatternBudget.bodyFactor_pos security) _ _ (by linarith [hs.1]) hs.2 target

def solution (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  Classical.choose (calibration_existsUnique security order horder hsecurity layout 1)

theorem solution_response (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    fullResponse security order horder (room security order horder hsecurity) layout (solution security order horder hsecurity layout) = 1 :=
  (Classical.choose_spec (calibration_existsUnique security order horder hsecurity layout 1)).1

theorem solution_unique (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) (coefficient : Family security order)
    (hresponse : fullResponse security order horder (room security order horder hsecurity) layout coefficient = 1) :
    coefficient = solution security order horder hsecurity layout :=
  (Classical.choose_spec (calibration_existsUnique security order horder hsecurity layout 1)).2.1 coefficient hresponse

theorem solution_norm (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    LocalRaisingBounds.coefficientNorm security order (solution security order horder hsecurity layout) ≤ 2 := by
  have hs := stable security order horder hsecurity layout
  have hbound := family_operator_norm_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) (hp security) (hb security)
    (fullResponse security order horder (room security order horder hsecurity) layout) _ (by linarith [hs.1]) hs.2
    (solution security order horder hsecurity layout)
  rw [solution_response, familyNorm_one] at hbound
  apply hbound.trans
  apply (div_le_iff₀ (by linarith [hs.1] : 0 < 1 - stabilityConstant order / (Parameters.base security : ℝ)^6)).mpr
  linarith [hs.1]

theorem solution_sub_one_norm (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    LocalRaisingBounds.coefficientNorm security order (solution security order horder hsecurity layout - 1) ≤
      2 * stabilityConstant order / (Parameters.base security : ℝ)^6 := by
  have hs := stable security order horder hsecurity layout
  have hnorm : LocalRaisingBounds.coefficientNorm security order (1 : Family security order) = 1 := familyNorm_one _ _ _ _ _
  have href := hs.2 1
  rw [hnorm, mul_one] at href
  have hbound := (Classical.choose_spec (calibration_existsUnique security order horder hsecurity layout 1)).2.2 1
  apply hbound.trans
  have hgap : 0 < 1 - stabilityConstant order / (Parameters.base security : ℝ)^6 := by linarith [hs.1]
  apply (div_le_div_of_nonneg_right href hgap.le).trans
  apply (div_le_iff₀ hgap).mpr
  have hnonneg : 0 ≤ stabilityConstant order / (Parameters.base security : ℝ)^6 :=
    div_nonneg (stabilityConstant_nonneg order) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hs.1 hnonneg
  rw [show 2 * stabilityConstant order / (Parameters.base security : ℝ)^6 =
    2 * (stabilityConstant order / (Parameters.base security : ℝ)^6) by ring]
  nlinarith only [hmul]

theorem solution_scalar (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    scalarHom (primaryLaw security) (bodyReference security) order (solution security order horder hsecurity layout) = 1 := by
  rw [← fullResponse_scalar security order horder (room security order horder hsecurity) layout, solution_response, map_one]

def coefficients (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : ActualControls.Coefficients security order :=
  familyCoefficientEquiv (primaryLaw security) (bodyReference security) order (solution security order horder hsecurity layout)

theorem coefficients_scalar (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    (coefficients security order horder hsecurity layout).1 = 1 := solution_scalar security order horder hsecurity layout

theorem coefficients_norm (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    ControlNorm.coefficientNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (coefficients security order horder hsecurity layout) ≤ 2 := by
  unfold coefficients
  rw [← familyNorm_eq_coefficientNorm]
  exact solution_norm security order horder hsecurity layout

theorem coefficient_unit (security order : ℕ) :
    familyCoefficientEquiv (primaryLaw security) (bodyReference security) order (1 : Family security order) = (1, 0) := by
  apply Prod.ext
  · change scalarHom (primaryLaw security) (bodyReference security) order (1 : Family security order) = 1
    exact map_one _
  · funext arity
    change (familyUnit (primaryLaw security) (bodyReference security) order) (positiveArity order arity) = 0
    rw [familyUnit, Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun output : TruncatedArity order => output.val.1.val + output.val.2.val) hequal
    have hpositive := arity.property.1
    change arity.val.1.val + arity.val.2.val = 0 + 0 at h
    omega

theorem coefficients_sub_one_norm (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    ControlNorm.coefficientNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (coefficients security order horder hsecurity layout - (1, 0)) ≤ 2 * stabilityConstant order / (Parameters.base security : ℝ)^6 := by
  rw [← coefficient_unit]
  change ControlNorm.coefficientNorm _ _ order _ _
    (familyCoefficientEquiv (primaryLaw security) (bodyReference security) order (solution security order horder hsecurity layout) -
      familyCoefficientEquiv (primaryLaw security) (bodyReference security) order 1) ≤ _
  have hequal := (familyCoefficientEquiv (primaryLaw security) (bodyReference security) order).map_sub
    (solution security order horder hsecurity layout) 1
  calc
    _ = ControlNorm.coefficientNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (familyCoefficientEquiv (primaryLaw security) (bodyReference security) order (solution security order horder hsecurity layout - 1)) :=
      (congrArg (ControlNorm.coefficientNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)) hequal).symm
    _ ≤ _ := by
      rw [← familyNorm_eq_coefficientNorm]
      exact solution_sub_one_norm security order horder hsecurity layout

theorem coefficientsToFamily_eq_solution (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    GradedControlAlgebra.coefficientsToFamily (primaryLaw security) (bodyReference security) order
      (coefficients security order horder hsecurity layout) = solution security order horder hsecurity layout :=
  GradedControlNorm.coefficientsToFamily_inverse _ _ _ _

/-- A public weight on the actual independent control pools at the fixed
placement. Its arguments contain no protected source or hidden input. -/
def publicWeight (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :=
  PhysicalSynthesis.coefficientWeight security order (Parameters.legCount security) (ordinaryPool security)
    (coefficients security order horder hsecurity layout)

theorem publicWeight_mass_one (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    kernelMean (PhysicalSynthesis.groupLaw security) (bodyReference security) (publicWeight security order horder hsecurity layout) = 1 :=
  PhysicalSynthesis.coefficientWeight_mass_one _ _ _ _ _ (coefficients_scalar security order horder hsecurity layout)

end
end CurrentAFT.ActualCompleteStability

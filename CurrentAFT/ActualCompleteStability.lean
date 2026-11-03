import CurrentAFT.ActualBackgroundInverse
import CurrentAFT.CompleteRaisingStability
import CurrentAFT.ActualRootFamily
import CurrentAFT.PhysicalSynthesis

/-! # Stability of the actual background and normalized response

Queue factors are multiplied before their true common-queue average. The
independent-root part below uses the constructed complete two-role raising
map and the actual averaged background. Root corrections are added only
through their actual finite-source operator.
-/
namespace CurrentAFT.ActualCompleteStability
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalCoefficientFamily
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
  BackgroundRates BackgroundLinear ActualBackground
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference BackgroundRates.ordinaryPool

private theorem hp (security : ℕ) : 0 ≤ primaryFactor security := (RaisingPatternBudget.primaryFactor_pos security).le
private theorem hb (security : ℕ) : 0 ≤ bodyFactor security := (RaisingPatternBudget.bodyFactor_pos security).le

private theorem norm_nonneg (security order : ℕ) (family : Family security order) :
    0 ≤ LocalRaisingBounds.coefficientNorm security order family :=
  familyNorm_nonneg _ _ order _ _ (hp security) (hb security) family

private theorem norm_add (security order : ℕ) (first second : Family security order) :
    LocalRaisingBounds.coefficientNorm security order (first + second) ≤
      LocalRaisingBounds.coefficientNorm security order first + LocalRaisingBounds.coefficientNorm security order second :=
  familyNorm_add_le _ _ order _ _ (hp security) (hb security) first second

private theorem norm_mul (security order : ℕ) (first second : Family security order) :
    LocalRaisingBounds.coefficientNorm security order (first * second) ≤
      LocalRaisingBounds.coefficientNorm security order first * LocalRaisingBounds.coefficientNorm security order second :=
  familyNorm_product_le _ _ order _ _ (hp security) (hb security) first second

theorem fixedQueueBackground_norm_decay (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : max order numericalThreshold ≤ security) (queue : ℤ) :
    LocalRaisingBounds.coefficientNorm security order (fixedQueueBackground security order horder queue - 1) ≤
      ActualBackground.stabilityConstant order / (Parameters.base security : ℝ)^6 := by
  apply (ActualBackground.fixedQueueBackground_norm security order horder hsecurity queue).trans_eq
  unfold budget ActualBackground.stabilityConstant
  ring

theorem fixedQueueBackground_norm_le_two (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : ActualBackgroundInverse.inverseThreshold order ≤ security) (queue : ℤ) :
    LocalRaisingBounds.coefficientNorm security order (fixedQueueBackground security order horder queue) ≤ 2 := by
  have hsmall := ActualBackgroundInverse.theta_le_half security order hsecurity
  have hlarge : max order numericalThreshold ≤ security :=
    (le_max_left _ _).trans hsecurity
  have hdefect := fixedQueueBackground_norm_decay security order horder hlarge queue
  have hsplit : fixedQueueBackground security order horder queue =
      (fixedQueueBackground security order horder queue - 1) + 1 := by abel
  calc
    _ = LocalRaisingBounds.coefficientNorm security order ((fixedQueueBackground security order horder queue - 1) + 1) := congrArg _ hsplit
    _ ≤ LocalRaisingBounds.coefficientNorm security order (fixedQueueBackground security order horder queue - 1) + 1 := by
      simpa only [LocalRaisingBounds.coefficientNorm, familyNorm_one] using norm_add security order (fixedQueueBackground security order horder queue - 1) 1
    _ ≤ 2 := by linarith

theorem fixedQueueBackground_norm_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ queue : ℤ,
      LocalRaisingBounds.coefficientNorm security order (fixedQueueBackground security order horder queue) ≤ 2 := by
  filter_upwards [eventually_ge_atTop (ActualBackgroundInverse.inverseThreshold order)] with security hsecurity queue
  exact fixedQueueBackground_norm_le_two security order horder hsecurity queue

theorem background_norm_le_two_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      LocalRaisingBounds.coefficientNorm security order (background security order horder) ≤ 2 := by
  filter_upwards [fixedQueueBackground_norm_eventually order horder] with security hbound
  exact certificateNorm_average_le security order (scalarLaw security) _ 2 (fun scalar => hbound scalar.val)

def independentResponse (security order : ℕ) (horder : 2 ≤ order) : Module.End ℝ (Family security order) where
  toFun family := background security order horder * (family + CompleteRaising.raisingLinear security order (by omega) family)
  map_add' first second := by rw [map_add]; simp only [mul_add]; abel
  map_smul' scalar family := by rw [map_smul]; simp only [← smul_add, mul_smul_comm, RingHom.id_apply]

def independentConstant (order : ℕ) : ℝ :=
  ActualBackground.stabilityConstant order + 2 * RaisingPatternNorm.stabilityConstant order

theorem independentConstant_nonneg (order : ℕ) : 0 ≤ independentConstant order := by
  unfold independentConstant ActualBackground.stabilityConstant
  exact add_nonneg (by positivity) (mul_nonneg (by norm_num) (CompleteRaisingStability.stabilityConstant_nonneg order))

theorem independentResponse_defect_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (family - independentResponse security order horder family) ≤
        (independentConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family := by
  filter_upwards [background_norm_decay_eventually order horder, background_norm_le_two_eventually order horder,
    CompleteRaisingStability.raising_norm_eventually order (by omega)] with security hbackground hbound hraising family
  have hbase : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hcost : RaisingPatternNorm.stabilityConstant order / (Parameters.base security : ℝ)^38 ≤
      RaisingPatternNorm.stabilityConstant order / (Parameters.base security : ℝ)^6 :=
    div_le_div_of_nonneg_left (CompleteRaisingStability.stabilityConstant_nonneg order)
      (pow_pos (FirstResponse.base_pos security) _) (pow_le_pow_right₀ hbase (by omega))
  have hsplit : family - independentResponse security order horder family =
      -((background security order horder - 1) * family + background security order horder * CompleteRaising.raisingLinear security order (by omega) family) := by
    change family - background security order horder * (family + _) = _
    rw [sub_mul, one_mul, mul_add]
    abel
  rw [hsplit]
  change familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security) (-_) ≤ _
  rw [familyNorm_neg]
  apply (norm_add security order _ _).trans
  apply (add_le_add (norm_mul security order _ _) (norm_mul security order _ _)).trans
  calc
    _ ≤ (ActualBackground.stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family +
        2 * ((RaisingPatternNorm.stabilityConstant order / (Parameters.base security : ℝ)^38) * LocalRaisingBounds.coefficientNorm security order family) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hbackground (norm_nonneg security order family))
        (mul_le_mul hbound (hraising family) (norm_nonneg security order _) (by norm_num))
    _ ≤ _ := by
      unfold independentConstant
      have h := mul_le_mul_of_nonneg_right hcost (norm_nonneg security order family)
      calc
        _ ≤ (ActualBackground.stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family +
          2 * ((RaisingPatternNorm.stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family) := by linarith
        _ = _ := by ring


def multiplyLinear (security order : ℕ) (multiplier : Family security order) : Module.End ℝ (Family security order) where
  toFun family := multiplier * family
  map_add' _ _ := mul_add _ _ _
  map_smul' _ _ := mul_smul_comm _ _ _

/-- The common public queue is sampled once. Its actual background factor
is multiplied by its actual root defect before averaging. -/
def rootCorrection (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : Module.End ℝ (Family security order) where
  toFun family := ∑ scalar : FirstHistogram.Scalar security, (scalarLaw security).weight scalar •
    (fixedQueueBackground security order horder scalar.val *
      ActualRootFamily.rootLinear security order (by omega) hroom scalar.val layout family)
  map_add' first second := by simp only [map_add, mul_add, smul_add, Finset.sum_add_distrib]
  map_smul' coefficient family := by
    simp only [map_smul, mul_smul_comm, Finset.smul_sum, smul_smul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro scalar _
    congr 1
    ring

def fullResponse (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : Module.End ℝ (Family security order) :=
  independentResponse security order horder + rootCorrection security order horder hroom layout

def stabilityConstant (order : ℕ) : ℝ :=
  independentConstant order + 2 * ActualRootDefectNorm.stabilityConstant order

theorem stabilityConstant_nonneg (order : ℕ) : 0 ≤ stabilityConstant order :=
  add_nonneg (independentConstant_nonneg order)
    (mul_nonneg (by norm_num) (ActualRootDefectNorm.stabilityConstant_nonneg order))

theorem rootCorrection_norm_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ hroom : 2 * order ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (rootCorrection security order horder hroom layout family) ≤
        (2 * ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ)^26) *
          LocalRaisingBounds.coefficientNorm security order family := by
  filter_upwards [fixedQueueBackground_norm_eventually order horder,
    ActualRootFamily.rootLinear_norm_eventually order (by omega)] with security hbackground hroot hroom layout family
  simp only [rootCorrection, LinearMap.coe_mk, AddHom.coe_mk]
  apply certificateNorm_average_le security order (scalarLaw security)
  intro scalar
  apply (norm_mul security order _ _).trans
  exact (mul_le_mul (hbackground scalar.val) (hroot hroom scalar.val layout family) (norm_nonneg security order _) (by norm_num)).trans_eq (by ring)

theorem fullResponse_defect_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ hroom : 2 * order ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (family - fullResponse security order horder hroom layout family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family := by
  filter_upwards [independentResponse_defect_eventually order horder, rootCorrection_norm_eventually order horder]
    with security hindependent hroot hroom layout family
  have hbase : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hcost : 2 * ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ)^26 ≤
      2 * ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ)^6 :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (ActualRootDefectNorm.stabilityConstant_nonneg order))
      (pow_pos (FirstResponse.base_pos security) _) (pow_le_pow_right₀ hbase (by omega))
  have hsplit : family - fullResponse security order horder hroom layout family =
      (family - independentResponse security order horder family) + -(rootCorrection security order horder hroom layout family) := by
    change family - (independentResponse security order horder family + rootCorrection security order horder hroom layout family) = _
    abel
  rw [hsplit]
  apply (norm_add security order _ _).trans
  change _ + familyNorm _ _ order _ _ (-_) ≤ _
  rw [familyNorm_neg]
  apply (add_le_add (hindependent family) (hroot hroom layout family)).trans
  have h := mul_le_mul_of_nonneg_right hcost (norm_nonneg security order family)
  unfold stabilityConstant
  calc
    _ ≤ (independentConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family +
      (2 * ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family := by linarith
    _ = _ := by ring

end
end CurrentAFT.ActualCompleteStability

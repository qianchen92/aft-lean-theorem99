import CurrentAFT.ActualRootDefectNorm
import CurrentAFT.MomentParameters
import CurrentAFT.UniformTaggedOutput

/-! # The complete averaged actual root operator on coefficient families -/
namespace CurrentAFT.ActualRootFamily
open AFT ActualBlockFock TaggedSelection UniformTaggedOutput ControlCoordinates ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
  LocalCoefficientFamily BackgroundRates
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance sumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool ProposalPrimary.primaryLaw ActualControls.bodyReference

theorem primary_room (security order : ℕ) (hroom : 2 * order ≤ security) (arity : TruncatedArity order) :
    arity.val.1.val ≤ Parameters.legCount security := by
  have h := FiniteAtomMoments.current_pool_room security order hroom arity.val.1.val arity.val.2.val arity.property
  omega

theorem body_room (security order : ℕ) (hroom : 2 * order ≤ security) (arity : TruncatedArity order) :
    arity.val.2.val ≤ ordinaryPool security := by
  have h := FiniteAtomMoments.current_pool_room security order hroom arity.val.1.val arity.val.2.val arity.property
  omega

/-- Every arity uses the actual independent uniform distinct selections,
including the scalar arity. The queue and public placement stay fixed. -/
def selectedAverage (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (arity : TruncatedArity order) :
    canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
      arity.val.1.val arity.val.2.val →ₗ[ℝ] Family security order where
  toFun kernel := ∑ choice : Choice security arity.val.1.val arity.val.2.val,
    ((choiceLaw security arity.val.1.val arity.val.2.val (primary_room security order hroom arity)
      (body_room security order hroom arity)).weight choice •
        ActualRootDefect.selectedDefect order horder queue
          (selection security arity.val.1.val arity.val.2.val choice) layout kernel : Family security order)
  map_add' first second := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' scalar kernel := by
    simp only [map_smul, Finset.smul_sum, smul_smul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro choice _
    rw [mul_comm]

theorem selectedAverage_apply (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (arity : TruncatedArity order)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
      arity.val.1.val arity.val.2.val) :
    selectedAverage security order horder hroom queue layout arity kernel =
      ∑ choice : Choice security arity.val.1.val arity.val.2.val,
        (choiceLaw security arity.val.1.val arity.val.2.val (primary_room security order hroom arity)
          (body_room security order hroom arity)).weight choice •
          ActualRootDefect.selectedDefect order horder queue
            (selection security arity.val.1.val arity.val.2.val choice) layout kernel := rfl

def rootLinear (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    Family security order →ₗ[ℝ] Family security order :=
  ∑ arity : TruncatedArity order,
    (selectedAverage security order horder hroom queue layout arity).comp (LinearMap.proj arity)

theorem rootLinear_apply (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (family : Family security order) :
    rootLinear security order horder hroom queue layout family =
      ∑ arity : TruncatedArity order, selectedAverage security order horder hroom queue layout arity (family arity) := by
  simp only [rootLinear, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

private theorem average_norm_le {Choice : Type*} [Fintype Choice] (security order : ℕ)
    (law : FiniteDist Choice) (terms : Choice → Family security order) (bound : ℝ)
    (hbound : ∀ choice, LocalRaisingBounds.coefficientNorm security order (terms choice) ≤ bound) :
    LocalRaisingBounds.coefficientNorm security order (∑ choice, law.weight choice • terms choice) ≤ bound := by
  apply (familyNorm_sum_le _ _ order _ _ (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le Finset.univ (fun choice => law.weight choice • terms choice)).trans
  calc
    _ ≤ ∑ choice, law.weight choice * bound := by
      apply Finset.sum_le_sum
      intro choice _
      rw [familyNorm_smul, abs_of_nonneg (law.nonneg choice)]
      exact mul_le_mul_of_nonneg_left (hbound choice) (law.nonneg choice)
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]

/-- The full actual root map is uniformly small after a fixed-order
threshold. Local positivity and current population thresholds are proved
from the public parameter family, rather than supplied as assumptions. -/
theorem rootLinear_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ hroom : 2 * order ≤ security, ∀ queue : ℤ,
      ∀ layout : BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (rootLinear security order horder hroom queue layout family) ≤
        (ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ) ^ 26) *
          LocalRaisingBounds.coefficientNorm security order family := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge
    (max (2 * LocalRaisingBounds.positiveConstant) LocalRaisingBounds.raisingConstant)
  filter_upwards [ActualRootDefectNorm.selectedDefect_norm_eventually order horder,
    eventually_ge_atTop threshold] with security hselected hsecurity
  intro hroom queue layout family
  have hbase : max (2 * LocalRaisingBounds.positiveConstant) LocalRaisingBounds.raisingConstant ≤
      (Parameters.base security : ℝ) := hthreshold.trans (Nat.cast_le.mpr (by unfold Parameters.base; omega))
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  have hlarge := (le_max_left _ _).trans hbase
  have hsmall : LocalRaisingBounds.raisingConstant ≤ (Parameters.base security : ℝ) ^ 38 := by
    apply ((le_max_right _ _).trans hbase).trans
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 38 by omega)
  have hbody := CycleSelections.current_body_fixed_orders order security hroom order le_rfl
  have haverage (arity : TruncatedArity order) :
      LocalRaisingBounds.coefficientNorm security order
        (selectedAverage security order horder hroom queue layout arity (family arity)) ≤
      (ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ) ^ 26) *
        (gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val *
          blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) (family arity).val) := by
    rw [selectedAverage_apply]
    apply average_norm_le
    intro choice
    exact hselected hlarge hsmall hbody arity.val.1.val arity.val.2.val arity.property
      (selection security arity.val.1.val arity.val.2.val choice) layout queue (family arity)
  rw [rootLinear_apply]
  apply (familyNorm_sum_le _ _ order _ _ (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le Finset.univ _).trans
  calc
    _ ≤ ∑ arity : TruncatedArity order,
        (ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ) ^ 26) *
          (gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val *
            blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) (family arity).val) :=
      Finset.sum_le_sum (fun arity _ => haverage arity)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem rootLinear_zero_constant (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (family : Family security order) :
    (rootLinear security order horder hroom queue layout family) (zeroArity order) = 0 := by
  rw [rootLinear_apply]
  simp_rw [selectedAverage_apply]
  simp only [Finset.sum_apply, Pi.smul_apply,
    ActualRootDefect.selectedDefect_zero_constant, smul_zero, Finset.sum_const_zero]

end
end CurrentAFT.ActualRootFamily

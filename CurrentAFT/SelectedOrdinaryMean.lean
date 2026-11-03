import CurrentAFT.SelectedOrdinaryRootProperties
import CurrentAFT.RootReferenceExpectation

/-! # Root averaging for a selected ordinary control

The body control is not resampled. These maps average or center only its
actual independent modular root, including when the root law has zero atoms.
-/
namespace CurrentAFT.SelectedOrdinaryMean
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert SelectedOrdinaryRoot
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

def rootMean (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (SafePalette security → ℝ) where
  toFun score center := (rootReference security).expectation (fun root => score (root, center))
  map_add' first second := by funext center; exact FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by funext center; exact FiniteDist.expectation_const_mul _ _ _

def constantRoot (security : ℕ) : (SafePalette security → ℝ) →ₗ[ℝ] (Input security → ℝ) where
  toFun score sample := score sample.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rootCenter (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Input security → ℝ) :=
  LinearMap.id - (constantRoot security).comp (rootMean security)

theorem rootMean_constant (security : ℕ) (score : SafePalette security → ℝ) :
    rootMean security (constantRoot security score) = score := by
  funext center
  change (rootReference security).expectation (fun _ => score center) = _
  rw [FiniteDist.expectation_const]

theorem rootCenter_constant (security : ℕ) (score : SafePalette security → ℝ) :
    rootCenter security (constantRoot security score) = 0 := by
  change constantRoot security score - constantRoot security (rootMean security (constantRoot security score)) = 0
  rw [rootMean_constant, sub_self]

theorem rootMean_energy_le (security : ℕ) (score : Input security → ℝ) :
    (bodyReference security).l2Sq (rootMean security score) ≤ (inputLaw security).l2Sq score := by
  unfold inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_comm]
  apply Finset.sum_le_sum
  intro center _
  apply mul_le_mul_of_nonneg_left _ ((bodyReference security).nonneg center)
  have h := (rootReference security).l2Sq_nonneg (centerLinear (rootReference security) (fun root => score (root, center)))
  rw [center_energy] at h
  exact sub_nonneg.mp h

theorem rootCenter_energy_le (security : ℕ) (score : Input security → ℝ) :
    (inputLaw security).l2Sq (rootCenter security score) ≤ (inputLaw security).l2Sq score := by
  unfold inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  conv_lhs => rw [FiniteDist.expectation_comm]
  conv_rhs => rw [FiniteDist.expectation_comm]
  apply Finset.sum_le_sum
  intro center _
  exact mul_le_mul_of_nonneg_left (center_energy_le (rootReference security) (fun root => score (root, center))) ((bodyReference security).nonneg center)

theorem rootCenter_centered (security : ℕ) (score : Input security → ℝ) (center : SafePalette security) :
    (rootReference security).expectation (fun root => rootCenter security score (root, center)) = 0 :=
  center_mean _ _

theorem rootMean_zero_of_centered (security : ℕ) (score : Input security → ℝ)
    (hcentered : ∀ center, (rootReference security).expectation (fun root => score (root, center)) = 0) :
    rootMean security score = 0 := funext hcentered

theorem rootCenter_eq_of_centered (security : ℕ) (score : Input security → ℝ)
    (hcentered : ∀ center, (rootReference security).expectation (fun root => score (root, center)) = 0) :
    rootCenter security score = score := by
  change score - constantRoot security (rootMean security score) = score
  rw [rootMean_zero_of_centered security score hcentered, map_zero, sub_zero]

theorem controlCenter_constant (security : ℕ) (score : SafePalette security → ℝ) :
    controlCenterLinear security (constantRoot security score) =
      constantRoot security (centerLinear (bodyReference security) score) := rfl

theorem push_root (security : ℕ) (root : Root security) (score : SafePalette security → ℝ)
    (output : Palette security) :
    pushLinear (bodyReference security) (rootEmbedding security root) score output =
      BodyChannelEvaluation.safeMass security score ((shiftEquiv security (root.val : ℤ)).symm output) := by
  unfold pushLinear rootEmbedding BodyChannelEvaluation.safeMass BodyChannelEvaluation.weightedEmbedding
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro center _
  have hequal : shiftEquiv security (root.val : ℤ) center.val = output ↔
      (shiftEquiv security (root.val : ℤ)).symm output = center.val := by
    constructor
    · intro h; exact ((shiftEquiv security (root.val : ℤ)).symm_apply_eq.mpr h.symm)
    · intro h; exact (Equiv.apply_eq_iff_eq_symm_apply (shiftEquiv security (root.val : ℤ))).mpr h.symm
  by_cases h : shiftEquiv security (root.val : ℤ) center.val = output
  · rw [if_pos h, if_pos (hequal.mp h), mul_one]
  · rw [if_neg h, if_neg (fun h' => h (hequal.mpr h')), mul_zero]

theorem rawMass_constant (security : ℕ) (score : SafePalette security → ℝ) :
    rawMass security (constantRoot security score) =
      MarkedPairLeading.bodyConvolution security (BodyChannelEvaluation.safeMass security score) := by
  funext output
  rw [rawMass_apply]
  change (rootReference security).expectation (fun root =>
    pushLinear (bodyReference security) (rootEmbedding security root) score output) = _
  simp only [push_root]
  change _ = (actualSeedLaw security).expectation (fun seed =>
    BodyChannelEvaluation.safeMass security score ((shiftEquiv security (actualBlur security seed)).symm output))
  apply RootReferenceExpectation.rootReference_seed_expectation security (fun value : ℤ =>
    BodyChannelEvaluation.safeMass security score ((shiftEquiv security value).symm output))
  intro first second hequal
  rw [RootBackgroundPolynomial.shiftEquiv_eq_of_cast security first second hequal]

end
end CurrentAFT.SelectedOrdinaryMean

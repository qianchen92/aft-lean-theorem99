import CurrentAFT.ConditionalHistogramMean
import CurrentAFT.WholeCycleMGF
import CurrentAFT.DriftMGF

/-! # The actual complete conditional histogram mean has a uniform MGF -/

namespace CurrentAFT.ConditionalHistogramMGF

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy UniformBodyProfiles
  ActualCycleMeanMGF ConditionalHistogramMean HistogramMean
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

/-- Literal finite expectation over the actual closed protected Gaussian
cycle, including every actual off-body endpoint marginal. -/
def moment (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (parameter : ℝ) : ℝ :=
  WholeCycleMGF.normalizedTotalMoment (Parameters.bodySize security) (Parameters.dimension security)
    (edgeLaw security) (response security (roles security layout) queue permutation)
    ((Parameters.legCount security : ℝ) • offBodyVector security) parameter

theorem moment_eq_expectation (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (parameter : ℝ) :
    moment security layout queue permutation parameter =
      (FiniteDist.independent (fun _ : BodyIndex security => edgeLaw security)).expectation
        (fun latent => Real.exp (parameter * ‖conditionalMean security layout queue permutation latent‖ ^ 2)) := rfl

theorem normalizedMean_eq_drift (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) :
    WholeCycleMGF.normalizedMean (Parameters.bodySize security) (Parameters.dimension security)
      (edgeLaw security) (response security (roles security layout) queue permutation)
      ((Parameters.legCount security : ℝ) • offBodyVector security) = drift security queue := by
  unfold WholeCycleMGF.normalizedMean
  rw [total_mean_vector security layout queue permutation]
  rfl

theorem moment_le (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (parameter : ℝ) (hparameter : 0 ≤ parameter) :
    moment security layout queue permutation parameter ≤
      Real.exp (2 * parameter * ‖drift security queue‖ ^ 2) *
        squareMoment security (roles security layout) queue permutation (2 * parameter) := by
  have h := WholeCycleMGF.total_moment_le (Parameters.bodySize security) (Parameters.dimension security)
    (edgeLaw security) (response security (roles security layout) queue permutation)
    ((Parameters.legCount security : ℝ) • offBodyVector security) parameter hparameter
  rw [normalizedMean_eq_drift] at h
  exact h

/-- Every fixed multiple of the current analysis-radius squared admits
one absolute moment bound, uniformly over the actual layout, body
permutation, and fixed common queue scalar. -/
theorem current_whole_mean_mgf_eventually (constant : ℝ) (hconstant : 0 ≤ constant) :
    ∃ threshold : ℕ, ∀ security ≥ threshold,
      ∀ layout : RoleIndex security ≃ BodyIndex security, ∀ queue : ℤ,
        ∀ permutation : Equiv.Perm (BodyIndex security),
          moment security layout queue permutation (constant * BackgroundRates.radius security ^ 2) ≤
            2 * Real.exp 2 := by
  have htwice : 0 ≤ 2 * constant := mul_nonneg (by norm_num) hconstant
  obtain ⟨cycleThreshold, hcycle⟩ := current_cycle_mean_mgf_eventually (2 * constant) htwice
  obtain ⟨driftThreshold, hdrift⟩ := DriftMGF.drift_exp_eventually (2 * constant) htwice
  refine ⟨max cycleThreshold driftThreshold, ?_⟩
  intro security hsecurity layout queue permutation
  have hc := hcycle security ((Nat.le_max_left _ _).trans hsecurity) (roles security layout) queue permutation
  have hd := hdrift security ((Nat.le_max_right _ _).trans hsecurity) queue
  have h := moment_le security layout queue permutation (constant * BackgroundRates.radius security ^ 2)
    (mul_nonneg hconstant (sq_nonneg _))
  have hparameter : 2 * (constant * BackgroundRates.radius security ^ 2) =
      (2 * constant) * BackgroundRates.radius security ^ 2 := by ring
  rw [hparameter] at h
  apply h.trans
  have hbound := mul_le_mul hd hc
    (CycleMeanMGF.normalizedCycleMoment_nonneg _ _ _ _ _)
    (Real.exp_nonneg _)
  apply hbound.trans_eq
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  ring

end

end CurrentAFT.ConditionalHistogramMGF

import CurrentAFT.ActualFockBound
import CurrentAFT.TaggedSelection

/-! # Actual complement mean MGF after distinct public control selections -/

namespace CurrentAFT.ComplementMeanMGF

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean ConditionalHistogramMGF
  PhysicalFockRates ActualFockBound TaggedSelection
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

def linear (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (multiple : ℝ)
    (latent : BodyIndex security → Edge security) (index : BlockIndex security)
    (color : ActualBlockMean.Palette security) : ℝ :=
  BlockProducts.normalizedLinear (Slots security) (uniformReference security)
    (rootedLaw security layout queue permutation latent)
    (normalizedScale security (Real.sqrt 2 * multiple)) index color

def keptEnergy (security r s : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (multiple : ℝ)
    (selection : Selection security r s) (latent : BodyIndex security → Edge security) : ℝ :=
  ∑ color, (∑ index ∈ selection.kept, linear security layout queue permutation multiple latent index color) ^ 2

theorem kept_linear_sum (security r s : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (multiple : ℝ)
    (selection : Selection security r s) (latent : BodyIndex security → Edge security)
    (color : ActualBlockMean.Palette security) :
    (∑ index : selection.kept, Real.sqrt 2 * BlockProducts.normalizedLinear
      (fun index : selection.kept => Slots security index.val) (uniformReference security)
      (fun index : selection.kept => rootedLaw security layout queue permutation latent index.val)
      (multiple * BackgroundRates.radius security / Real.sqrt (Parameters.dimension security : ℝ)) index color) =
      ∑ index ∈ selection.kept, linear security layout queue permutation multiple latent index color := by
  have hpoint (index : selection.kept) : Real.sqrt 2 * BlockProducts.normalizedLinear
      (fun index : selection.kept => Slots security index.val) (uniformReference security)
      (fun index : selection.kept => rootedLaw security layout queue permutation latent index.val)
      (multiple * BackgroundRates.radius security / Real.sqrt (Parameters.dimension security : ℝ)) index color =
      linear security layout queue permutation multiple latent index.val color := by
    unfold linear BlockProducts.normalizedLinear BlockProducts.localCoefficient normalizedScale
    ring
  simp_rw [hpoint]
  exact (Finset.sum_subtype selection.kept (fun _ => Iff.rfl)
    (fun index => linear security layout queue permutation multiple latent index color)).symm

/-- The threshold depends only on the fixed radius multiple. All selected
positions and all closed-cycle roots are genuine; the sole order cost is
the explicit number `2*r+s` of deleted independent physical blocks. -/
theorem current_complement_mean_mgf_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold,
      ∀ r s : ℕ, ∀ selection : Selection security r s,
      ∀ layout : RoleIndex security ≃ BodyIndex security, ∀ queue : ℤ,
      ∀ permutation : Equiv.Perm (BodyIndex security),
        (latentLaw security).expectation (fun latent =>
          Real.exp (8 * keptEnergy security r s layout queue permutation multiple selection latent)) ≤
          2 * Real.exp (2 * ((2 * r + s : ℕ) : ℝ) + 2) := by
  have hm : 0 ≤ Real.sqrt 2 * multiple := mul_nonneg (Real.sqrt_nonneg _) hmultiple
  obtain ⟨activityThreshold, hactivity⟩ := envelopes_eventually (Real.sqrt 2 * multiple) hm
  obtain ⟨meanThreshold, hmean⟩ := current_whole_mean_mgf_eventually (16 * (Real.sqrt 2 * multiple) ^ 2) (by positivity)
  refine ⟨max activityThreshold meanThreshold, ?_⟩
  intro security hsecurity r s selection layout queue permutation
  have hremoved : (OmittedBlockMean.removed selection.kept).card ≤ 2 * r + s := by
    rw [selection.removed_complement, selection.removed_card]
  have hlinear (latent : BodyIndex security → Edge security) :
      (∑ index, ∑ color, linear security layout queue permutation multiple latent index color ^ 2) ≤ 1 / 8 := by
    exact (linearActivity_le security (attachmentRoots security layout permutation latent)
      (centerRoots security layout permutation latent) (queueRoots security layout permutation latent)
      (normalizedScale security (Real.sqrt 2 * multiple)) queue).trans
      (hactivity security ((Nat.le_max_left _ _).trans hsecurity)).1
  have h := OmittedBlockMean.omitted_square_mgf_le (latentLaw security) selection.kept
    (linear security layout queue permutation multiple) (2 * r + s) hremoved hlinear
  have hidentity := mean_exponential_identity_parameter security layout queue permutation (Real.sqrt 2 * multiple) 16
  change _ = _ at hidentity
  change (latentLaw security).expectation (fun latent => Real.exp (8 * keptEnergy security r s layout queue permutation multiple selection latent)) ≤
    Real.exp (2 * ((2 * r + s : ℕ) : ℝ)) * (latentLaw security).expectation (fun latent =>
      Real.exp (16 * ∑ color, (∑ index, BlockProducts.normalizedLinear (Slots security) (uniformReference security)
        (rootedLaw security layout queue permutation latent) (normalizedScale security (Real.sqrt 2 * multiple)) index color) ^ 2)) at h
  rw [hidentity] at h
  apply h.trans
  have hm' := hmean security ((Nat.le_max_right _ _).trans hsecurity) layout queue permutation
  apply (mul_le_mul_of_nonneg_left hm' (Real.exp_nonneg _)).trans_eq
  rw [Real.exp_add]
  ring

end

end CurrentAFT.ComplementMeanMGF

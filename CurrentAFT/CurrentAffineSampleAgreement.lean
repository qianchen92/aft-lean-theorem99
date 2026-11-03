import CurrentAFT.CurrentAffinePhysicalEndpoint
import CurrentAFT.CurrentAffineTransport

/-! # The actual public sample realizes the completed physical endpoint

The public closing edge is the same finite sampled edge in both
descriptions. The protected hidden word is not resampled for the carry or
physical endpoint conclusions.
-/
namespace CurrentAFT.CurrentAffineSampleAgreement

open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentSourceProtection CurrentSourceLayout CurrentHiddenSourceTransport
  CurrentPublicAffineSample CurrentAffinePhysicalEndpoint GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def sourceWord (security : ℕ) (sample : Sample security) (input : HiddenWord security) :
    ProtectedWord (cutoff security) := joinProtected security (input, sample.2)

def physicalWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (sample : Sample security) (input : HiddenWord security) : CurrentZeroFiber.Word security :=
  fun index => RefinedPublicOutput.embed security
    (outputWord security layout sample.1.1 sample.1.2 (sourceWord security sample input) index)

theorem endpoint_physical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (sample : Sample security) (hsample : (law security weight hpositive).weight sample ≠ 0)
    (input : HiddenWord security) :
    CurrentAffineTransport.endpoint security layout sample (sourceEmbedding (hiddenCutoff security) input) =
      physicalWord security layout sample input := by
  have hs := support security weight hpositive sample hsample
  have hsplit := (splitWord security).apply_symm_apply
    (sourceEmbedding (hiddenCutoff security) input, sample.2.val)
  have hh : hiddenWord security (sourceEmbedding (cutoff security) (sourceWord security sample input)) =
      sourceEmbedding (hiddenCutoff security) input := congrArg Prod.fst hsplit
  have hc : closureScalar security (sourceEmbedding (cutoff security) (sourceWord security sample input)) =
      sample.2.val := congrArg Prod.snd hsplit
  have h := affine_mod_output security layout sample.1.1 sample.1.2 hs.1.1 (sourceWord security sample input)
  rw [hh, hc] at h
  unfold CurrentAffineTransport.endpoint
  rw [realize_on_support security layout weight hpositive sample hsample]
  exact h

/-- The same realized affine output is the canonical pullback of the
completed physical endpoint, on every supported public sample and every
protected hidden source vector. -/
theorem output_physical_pullback (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (sample : Sample security) (hsample : (law security weight hpositive).weight sample ≠ 0)
    (input : HiddenWord security) :
    CurrentAffineTransport.output security layout sample (sourceEmbedding (hiddenCutoff security) input) =
      CurrentZeroFiber.pullback security (physicalWord security layout sample input) := by
  rw [← endpoint_physical security layout weight hpositive sample hsample input]
  exact (CurrentZeroFiber.pullback_rounding security _
    (CurrentAffineTransport.supported_protected_carry security layout weight hpositive sample hsample input)).symm

end
end CurrentAFT.CurrentAffineSampleAgreement

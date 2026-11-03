import CurrentAFT.CurrentAffineSampleAgreement
import CurrentAFT.CurrentProtectedAffineLaw

/-! # Regrouping the actual finite public and protected source draws -/
namespace CurrentAFT.CurrentProtectedSampleFubini
open AFT CurrentSourceProtection CurrentSourceLayout CurrentHiddenSourceTransport
  CurrentPublicAffineSample CurrentAffinePhysicalEndpoint CurrentAffineSampleAgreement
  GaussianProductProtection ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem regroup_public_source {Public Charts Output : Type*}
    [Fintype Public] [Fintype Charts] [Fintype Output]
    (security : ℕ) (publicLaw : FiniteDist Public) (chartLaw : Public → FiniteDist Charts)
    (value : Public → Charts → ProtectedWord (cutoff security) → Output) :
    ((FiniteDist.joint publicLaw chartLaw).prod (closureLaw security)).mix
      (fun sample => (hiddenLaw security).map (fun input =>
        value sample.1.1 sample.1.2 (joinProtected security (input, sample.2)))) =
      publicLaw.mix (fun publicDraw => (chartLaw publicDraw).mix (fun charts =>
        (protectedSourceLaw security).map (value publicDraw charts))) := by
  rw [← protected_law_join security]
  simp_rw [FiniteDist.map_map]
  ext output
  simp only [FiniteDist.mix_weight, FiniteDist.map_weight, FiniteDist.prod_weight,
    FiniteDist.joint, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro publicDraw _
  apply Finset.sum_congr rfl
  intro charts _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  apply Finset.sum_congr rfl
  intro closure _
  split_ifs <;> ring

def corePhysicalLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) : FiniteDist (CurrentZeroFiber.Word security) :=
  (chartsLaw security core).mix (fun charts => (protectedSourceLaw security).map
    (fun word index => RefinedPublicOutput.embed security (outputWord security layout core charts word index)))

theorem protectedEndpoint_eq_corePhysical (security : ℕ)
    (layout : RoleIndex security ≃ BodyIndex security) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    CurrentAffineTransport.protectedEndpointLaw security layout weight hpositive =
      (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).mix
        (corePhysicalLaw security layout) := by
  calc
    _ = (law security weight hpositive).mix (fun sample => (hiddenLaw security).map
        (physicalWord security layout sample)) := by
      apply FiniteDist.mix_congr_support
      intro sample hsample
      congr 1
      funext input
      exact endpoint_physical security layout weight hpositive sample hsample input
    _ = _ := regroup_public_source security
      (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive)
      (chartsLaw security) (fun core charts word index =>
        RefinedPublicOutput.embed security (outputWord security layout core charts word index))

theorem corePhysical_eq_completed (security : ℕ)
    (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    corePhysicalLaw security layout core =
      FiniteDist.retype (ActualAffineCompletedOutput.mappedChannel security layout core) := by
  rw [← CurrentProtectedAffineLaw.protectedChartMapped_eq]
  unfold corePhysicalLaw CurrentProtectedAffineLaw.protectedChartMapped
    CurrentProtectedAffineLaw.protectedChartPalette
  simp only [FiniteDist.map_mix, FiniteDist.map_map]
  ext word
  simp only [FiniteDist.retype_weight, FiniteDist.mix_weight, FiniteDist.map_weight]
  apply Finset.sum_congr (by ext charts; simp)
  intro charts _
  apply congrArg₂ (fun first second : ℝ => first * second) rfl
  apply Finset.sum_congr (by ext source; simp)
  intro source _
  split_ifs <;> rfl

theorem protectedEndpoint_eq_completed (security : ℕ)
    (layout : RoleIndex security ≃ BodyIndex security) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    CurrentAffineTransport.protectedEndpointLaw security layout weight hpositive =
      (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).mix
        (fun core => FiniteDist.retype (ActualAffineCompletedOutput.mappedChannel security layout core)) := by
  rw [protectedEndpoint_eq_corePhysical]
  congr 1
  funext core
  exact corePhysical_eq_completed security layout core

end
end CurrentAFT.CurrentProtectedSampleFubini

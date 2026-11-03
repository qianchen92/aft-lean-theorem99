import CurrentAFT.CurrentCoreProposalLaw

/-! The stored buffers are a representation of the public core, with no
additional sampling freedom in the chart-input vector or inverse rows. -/
namespace CurrentAFT.CurrentCoreProposal
open AFT CurrentProposalDimensions
set_option maxHeartbeats 700000
attribute [local irreducible] CurrentProposalDimensions.current Parameters.legCount Parameters.dimension Parameters.bodySize

 theorem materialized_core_injective (security : ℕ) : Function.Injective (@MaterializedCore.core security) := by
  intro first second hequal
  have hc : first.controls = second.controls := by
    apply Vector.ext
    intro index hindex
    have h := congrArg (fun core : ActualPublicCharge.Core security =>
      core.controls (controlsEquiv security ⟨index, hindex⟩)) hequal
    simpa only [MaterializedCore.core, decode, Equiv.symm_apply_apply] using h
  have hl : first.legs = second.legs := by
    apply Vector.ext
    intro index hindex
    have h := congrArg (fun core : ActualPublicCharge.Core security =>
      core.legs (legEquiv security ⟨index, hindex⟩)) hequal
    simpa only [MaterializedCore.core, decode, Equiv.symm_apply_apply] using h
  have hq : first.baselines = second.baselines := by
    apply Vector.ext
    intro index hindex
    have h := congrArg (fun core : ActualPublicCharge.Core security =>
      core.queueBaselines (queueEquiv security ⟨index, hindex⟩)) hequal
    simpa only [MaterializedCore.core, decode, Equiv.symm_apply_apply] using h
  have hb : first.body = second.body := by
    apply (CurrentPermutationDraw.cachedEquiv (current security).body).injective
    apply (CurrentProposalDimensions.bodyEquiv security).permCongr.injective
    exact congrArg ActualPublicCharge.Core.bodyPermutation hequal
  have he : first.endpoints = second.endpoints := by
    apply (CurrentPermutationDraw.cachedEquiv (current security).dimension).injective
    apply (endpointEquiv security).permCongr.injective
    exact congrArg ActualPublicCharge.Core.endpointPermutation hequal
  have hi : first.inputs = second.inputs := by
    apply Vector.ext
    intro index hindex
    change first.inputs.get ⟨index, hindex⟩ = second.inputs.get ⟨index, hindex⟩
    rw [first.inputs_correct, second.inputs_correct, hc, hl]
  cases first
  cases second
  cases hc
  cases hl
  cases hq
  cases hb
  cases he
  cases hi
  rfl

noncomputable instance materializedCoreFintype (security : ℕ) : Fintype (MaterializedCore security) :=
  Fintype.ofInjective MaterializedCore.core (materialized_core_injective security)

noncomputable def materializedLaw (security tableBits bits : ℕ) (cache : CurrentReferenceDraw.Cache security tableBits) :
    FiniteDist (MaterializedCore security) :=
  (CurrentCoreProposalLaw.tapeLaw security bits).map (fun word => (draw security tableBits bits cache word).value)

 theorem materializedLaw_core (security tableBits bits : ℕ) (cache : CurrentReferenceDraw.Cache security tableBits) :
    (materializedLaw security tableBits bits cache).map MaterializedCore.core =
      CurrentCoreProposalLaw.law security tableBits bits cache := by
  rw [materializedLaw, FiniteDist.map_map]
  rfl

end CurrentAFT.CurrentCoreProposal

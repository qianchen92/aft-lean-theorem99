import CurrentAFT.AffineLegCompletion

/-!
# Complete protected output after public affine-chart completion

All roots, queue scalars and permutations are the actual ones.  Each
protected leg uses the complete source-independent public chart law; the
ordinary and queue channels are unchanged.  Averaging auxiliary activation
bits is exactly this completed output, even with the entire remaining core
fixed.
-/

namespace CurrentAFT.ActualAffineCompletedOutput

open AFT AffineFlagCalibration ActualPublicCharge DiffuseProfiles ProposalPrimary
  ActualBlockFock ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean
  PublicOutputExperiment PublicCoefficientOutput PublicAuxiliaryFubini
open HistogramNormalization PhysicalSynthesis
open scoped BigOperators Classical

noncomputable section

local instance completedOutputFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def activationBitsLaw (security : ℕ) : FiniteDist (Fin (Parameters.legCount security) → Bool) :=
  FiniteDist.independent (fun _ => ActualPublicLegCharge.activationLaw security)

def blocks (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    (index : BlockIndex security) → FiniteDist (Slots security index → RefinedPublicOutput.Palette security)
  | .inl leg => completedTriple security (attachmentRoots security layout core.bodyPermutation latent leg)
      (core.controls (.inl leg)).1 (core.legs leg)
  | .inr (.inl center) => RefinedPublicOutput.singleton security
      (centerRoots security layout core.bodyPermutation latent center)
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val
  | .inr (.inr point) => RefinedPublicOutput.singleton security
      (queueRoots security layout core.bodyPermutation latent point + queue) (core.queueBaselines point)

def conditionalLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    FiniteDist (Sigma (Slots security) → RefinedPublicOutput.Palette security) :=
  FiniteDist.retype (BlockProducts.blockLaw (Slots security) (blocks security layout core queue latent))

theorem conditional_activation_average (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    (activationBitsLaw security).mix (fun bits =>
      RefinedPublicOutput.conditionalLaw security layout (setActivationBits security core bits) queue latent) =
      conditionalLaw security layout core queue latent := by
  ext word
  simp only [FiniteDist.mix_weight, RefinedPublicOutput.conditionalLaw, conditionalLaw,
    FiniteDist.retype_weight, BlockProducts.blockLaw, BlockProducts.blockMass,
    Fintype.prod_sum_type, RefinedPublicOutput.blocks, blocks]
  change (activationBitsLaw security).expectation (fun bits =>
      (∏ leg, (RefinedPublicOutput.triple security
        (attachmentRoots security layout core.bodyPermutation latent leg)
        (core.controls (.inl leg)).1 (setMarked security (core.legs leg).1 (bits leg), (core.legs leg).2)).weight
          (fun slot => word ⟨.inl leg, slot⟩)) *
      ((∏ center, (RefinedPublicOutput.singleton security
        (centerRoots security layout core.bodyPermutation latent center)
        (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val).weight
          (fun slot => word ⟨.inr (.inl center), slot⟩)) *
       ∏ point, (RefinedPublicOutput.singleton security
        (queueRoots security layout core.bodyPermutation latent point + queue) (core.queueBaselines point)).weight
          (fun slot => word ⟨.inr (.inr point), slot⟩))) = _
  rw [FiniteDist.expectation_mul_const]
  apply congrArg₂ (· * ·) _ rfl
  trans ∏ leg : Fin (Parameters.legCount security),
    (ActualPublicLegCharge.activationLaw security).expectation (fun flag =>
      (RefinedPublicOutput.triple security (attachmentRoots security layout core.bodyPermutation latent leg)
        (core.controls (.inl leg)).1 (setMarked security (core.legs leg).1 flag, (core.legs leg).2)).weight
          (fun slot => word ⟨.inl leg, slot⟩))
  · exact independent_product (fun _ : Fin (Parameters.legCount security) =>
      ActualPublicLegCharge.activationLaw security) (fun leg flag =>
        (RefinedPublicOutput.triple security (attachmentRoots security layout core.bodyPermutation latent leg)
          (core.controls (.inl leg)).1 (setMarked security (core.legs leg).1 flag, (core.legs leg).2)).weight
            (fun slot => word ⟨.inl leg, slot⟩))
  apply Finset.prod_congr rfl
  intro leg _
  have hl := congrArg (fun law => law.weight (fun slot => word ⟨.inl leg, slot⟩))
    (completedTriple_reference security (attachmentRoots security layout core.bodyPermutation latent leg)
      (core.controls (.inl leg)).1 (core.legs leg))
  exact hl.symm

def lawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security) :=
  (scalarLaw security).mix (fun queue => (FiniteDist.retype (ActualFockBound.latentLaw security)).mix
    (fun latent => (conditionalLaw security layout core queue.val latent).map
      (fun word => AFT.relabel (renameWord (flatten security) word) core.endpointPermutation)))

theorem activation_average (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) :
    (activationBitsLaw security).mix (fun bits =>
      RefinedPublicOutput.lawGiven security layout (setActivationBits security core bits)) =
        lawGiven security layout core := by
  unfold RefinedPublicOutput.lawGiven lawGiven
  rw [FiniteDist.mix_comm]
  apply congrArg (FiniteDist.mix (scalarLaw security))
  funext queue
  rw [FiniteDist.mix_comm]
  apply congrArg (FiniteDist.mix (FiniteDist.retype (ActualFockBound.latentLaw security)))
  funext latent
  change (activationBitsLaw security).mix (fun bits =>
    (RefinedPublicOutput.conditionalLaw security layout (setActivationBits security core bits)
      queue.val latent).map (fun word => AFT.relabel (renameWord (flatten security) word) core.endpointPermutation)) = _
  rw [← FiniteDist.map_mix, conditional_activation_average]

def mappedChannel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → RefinedPublicOutput.Residue security) :=
  (lawGiven security layout core).map (fun word index => RefinedPublicOutput.embed security (word index))

theorem mapped_activation_average (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) :
    (activationBitsLaw security).mix (fun bits =>
      RefinedPublicOutput.mappedChannel security layout (setActivationBits security core bits)) =
        mappedChannel security layout core := by
  unfold RefinedPublicOutput.mappedChannel mappedChannel
  rw [← FiniteDist.map_mix, activation_average]

end
end CurrentAFT.ActualAffineCompletedOutput

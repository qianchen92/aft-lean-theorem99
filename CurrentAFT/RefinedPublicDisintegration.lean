import CurrentAFT.RefinedPublicOutput
import CurrentAFT.PublicAuxiliaryFubini
import CurrentAFT.RefinedPublicTripleAverage

/-! # Averaging only the newly exposed public coordinates -/
namespace CurrentAFT.RefinedPublicDisintegration
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean ActualPublicCharge PublicOutputExperiment PublicCoefficientOutput
  PositivePublicChannels RefinedPublicOutput PublicAuxiliaryFubini
open scoped BigOperators Classical
noncomputable section
section Local
local instance disintegrationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

private theorem conditional_average_of_local (security : ℕ)
    (htriple : ∀ root primary word, (legCoreLaw security).expectation (fun seed =>
      (triple security root primary seed).weight word) = (tripleGiven security root primary).weight word)
    (hsingleton : ∀ root word, (safeLaw security).expectation (fun center =>
      (singleton security root center).weight word) =
        (singletonLaw ((safeLaw security).map (shiftEquiv security root))).weight word)
    (layout : RoleIndex security ≃ BodyIndex security) (controls : PublicWord security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (endpointPermutation : Equiv.Perm (Fin (Parameters.dimension security)))
    (latent : BodyIndex security → Edge security) (word : Sigma (Slots security) → RefinedPublicOutput.Palette security) :
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).expectation
      (fun legs => (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => safeLaw security)).expectation
        (fun baselines => (RefinedPublicOutput.conditionalLaw security layout
          ⟨controls, legs, baselines, permutation, endpointPermutation⟩ queue latent).weight word)) =
      (FiniteDist.retype (PublicOutputExperiment.conditionalLaw security layout queue permutation latent controls)).weight word := by
  simp only [RefinedPublicOutput.conditionalLaw, PublicOutputExperiment.conditionalLaw,
    FiniteDist.retype_weight, BlockProducts.blockLaw, BlockProducts.blockMass,
    Fintype.prod_sum_type, RefinedPublicOutput.blocks, PublicOutputExperiment.conditionalBlocks]
  apply Eq.trans (independent_pair_product
    (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)
    (fun _ : Fin (Parameters.modulus security) => safeLaw security)
    (fun leg seed => (triple security (attachmentRoots security layout permutation latent leg)
      (controls (.inl leg)).1 seed).weight (fun slot => word ⟨.inl leg, slot⟩))
    (fun point center => (RefinedPublicOutput.singleton security
      (queueRoots security layout permutation latent point + queue) center).weight
      (fun slot => word ⟨.inr (.inr point), slot⟩))
    (∏ center, (RefinedPublicOutput.singleton security (centerRoots security layout permutation latent center)
      (controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val).weight
      (fun slot => word ⟨.inr (.inl center), slot⟩)))
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro leg _
    exact htriple _ _ _
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro center _
      rfl
    · apply Finset.prod_congr rfl
      intro point _
      exact hsingleton _ _

private theorem conditional_average_local (security : ℕ)
    (layout : RoleIndex security ≃ BodyIndex security) (controls : PublicWord security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (endpointPermutation : Equiv.Perm (Fin (Parameters.dimension security)))
    (latent : BodyIndex security → Edge security) (word : Sigma (Slots security) → RefinedPublicOutput.Palette security) :
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).expectation
      (fun legs => (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => safeLaw security)).expectation
        (fun baselines => (RefinedPublicOutput.conditionalLaw security layout
          ⟨controls, legs, baselines, permutation, endpointPermutation⟩ queue latent).weight word)) =
      (FiniteDist.retype (PublicOutputExperiment.conditionalLaw security layout queue permutation latent controls)).weight word := by
  apply conditional_average_of_local
  · intro root primary word
    exact congrArg (fun law => law.weight word) (RefinedPublicTripleAverage.triple_average security root primary)
  · intro root word
    exact congrArg (fun law => law.weight word) (RefinedPublicTripleAverage.singleton_average security root)

end Local
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem conditional_average (security : ℕ)
    (layout : RoleIndex security ≃ BodyIndex security) (controls : PublicWord security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (endpointPermutation : Equiv.Perm (Fin (Parameters.dimension security)))
    (latent : BodyIndex security → Edge security) (word : Sigma (Slots security) → RefinedPublicOutput.Palette security) :
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).expectation
      (fun legs => (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => safeLaw security)).expectation
        (fun baselines => (FiniteDist.retype (RefinedPublicOutput.conditionalLaw security layout
          ⟨controls, legs, baselines, permutation, endpointPermutation⟩ queue latent)).weight word)) =
      (PublicOutputExperiment.conditionalLaw security layout queue permutation latent controls).weight word := by
  convert conditional_average_local security layout controls queue permutation endpointPermutation latent word using 1
  simp only [FiniteDist.retype_weight]
  apply Eq.trans (TensorPublicProjection.independent_decision_expectation
    (inferInstance : DecidableEq (Fin (Parameters.legCount security))) (Classical.decEq _)
    (fun _ => legCoreLaw security) _)
  congr 1
  funext legs
  exact TensorPublicProjection.independent_decision_expectation
    (inferInstance : DecidableEq (Fin (Parameters.modulus security))) (Classical.decEq _)
    (fun _ => safeLaw security) _

theorem coarse_weight (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (controls : PublicWord security) (word : Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security) :
    (PublicSignedOutput.lawGiven security layout controls).weight word =
      (endpointPermutationLaw security).expectation (fun endpoints =>
        (scalarLaw security).expectation (fun queue => (bodyPermutationLaw security).expectation (fun body =>
          (FiniteDist.retype (ActualFockBound.latentLaw security)).expectation (fun latent =>
            (PublicOutputExperiment.conditionalLaw security layout queue.val body latent controls).weight
              ((outputEquiv security endpoints).symm word))))) := by
  unfold PublicSignedOutput.lawGiven
  rw [AFT.symmetrize_eq_permutation_mix]
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  change (endpointPermutationLaw security).expectation (fun endpoints =>
    (PublicSignedOutput.rawLawGiven security layout controls).weight ((AFT.relabelEquiv endpoints).symm word)) = _
  apply congrArg (FiniteDist.expectation _)
  funext endpoints
  unfold PublicSignedOutput.rawLawGiven PublicCoefficientOutput.outputLawGiven
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  change (FiniteDist.retype (ActualWeightedFourier.randomizationLaw security)).expectation (fun sample =>
    (FiniteDist.retype (ActualFockBound.latentLaw security)).expectation (fun latent =>
      (PublicOutputExperiment.conditionalLaw security layout sample.1.val sample.2 latent controls).weight
        ((outputEquiv security endpoints).symm word))) = _
  unfold ActualWeightedFourier.randomizationLaw bodyPermutationLaw
  rw [expectation_retype_prod, retype_uniform]
  simp only [FiniteDist.expectation_retype]

/-- Exposing all source-independent public seeds changes no output
probability. The protected queue scalar and the complete latent cycle
remain inside the conditional channel on both sides. -/
theorem refined_average (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (controls : PublicWord security) (word : Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security) :
    (auxiliaryLaw security controls).expectation (fun core =>
      (FiniteDist.retype (RefinedPublicOutput.lawGiven security layout core)).weight word) =
      (PublicSignedOutput.lawGiven security layout controls).weight word := by
  conv_rhs => rw [coarse_weight]
  rw [auxiliary_expectation]
  simp_rw [FiniteDist.retype_weight, RefinedPublicOutput.lawGiven_weight, FiniteDist.expectation_retype]
  apply Eq.trans (@five_expectation_interchange _ _ _ _ _
    (enumeration (localSeedsLaw security)) (enumeration (bodyPermutationLaw security))
    (enumeration (endpointPermutationLaw security)) (enumeration (scalarLaw security))
    (enumeration (ActualFockBound.latentLaw security))
    (localSeedsLaw security) (bodyPermutationLaw security) (endpointPermutationLaw security)
    (scalarLaw security) (ActualFockBound.latentLaw security)
    (fun seeds body endpoints queue latent =>
      (FiniteDist.retype (RefinedPublicOutput.conditionalLaw security layout
        ⟨controls, seeds.1, seeds.2, body, endpoints⟩ queue.val latent)).weight
          ((outputEquiv security endpoints).symm word)))
  apply congrArg (@FiniteDist.expectation _ (enumeration (endpointPermutationLaw security)) (endpointPermutationLaw security))
  funext endpoints
  apply congrArg (@FiniteDist.expectation _ (enumeration (scalarLaw security)) (scalarLaw security))
  funext queue
  apply congrArg (@FiniteDist.expectation _ (enumeration (bodyPermutationLaw security)) (bodyPermutationLaw security))
  funext body
  apply congrArg (@FiniteDist.expectation _ (enumeration (ActualFockBound.latentLaw security)) (ActualFockBound.latentLaw security))
  funext latent
  unfold localSeedsLaw
  rw [FiniteDist.expectation_prod]
  exact conditional_average security layout controls queue.val body endpoints latent _

end
end CurrentAFT.RefinedPublicDisintegration

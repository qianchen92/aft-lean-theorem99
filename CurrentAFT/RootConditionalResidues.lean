import CurrentAFT.TypedTaggedPhysical
import CurrentAFT.RootSelectedZeroTag
import CurrentAFT.ActualLayouts

/-! # Integer roots and residue roots give the identical full conditional PGF -/
namespace CurrentAFT.RootConditionalResidues
open AFT ActualBlockFock TaggedSelection JointTaggedPhysicalFock TaggedPhysicalFock
  OrdinaryPhysicalFock TypedTaggedPhysical RootBackgroundPolynomial ActualLayouts
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean CycleRootExpansion ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

theorem averagedPairedChannel_periodic (security : ℕ) (firstComp secondComp firstAttach secondAttach : ℤ)
    (hcomp : (firstComp : Root security) = (secondComp : Root security))
    (hattach : (firstAttach : Root security) = (secondAttach : Root security)) :
    averagedPairedChannel security firstComp firstAttach = averagedPairedChannel security secondComp secondAttach := by
  apply LinearMap.ext
  intro score
  simp only [averagedPairedChannel_apply,
    RootSelectedZeroTag.pairedMassAt_periodic security firstComp secondComp firstAttach secondAttach hcomp hattach]

theorem bodyChannel_periodic (security : ℕ) (first second : ℤ)
    (hequal : (first : Root security) = (second : Root security)) :
    bodyChannel security first = bodyChannel security second := by
  ext score word
  simp only [bodyChannel, translatedProfile,
    shiftEquiv_eq_of_cast security first second hequal]

theorem physicalChannel_periodic (security r s : ℕ)
    (firstComp secondComp firstAttach secondAttach : Fin r → ℤ) (firstBody secondBody : Fin s → ℤ)
    (hcomp : ∀ index, (firstComp index : Root security) = (secondComp index : Root security))
    (hattach : ∀ index, (firstAttach index : Root security) = (secondAttach index : Root security))
    (hbody : ∀ index, (firstBody index : Root security) = (secondBody index : Root security))
    (index : Fin (r + s)) :
    physicalChannel security r s firstComp firstAttach firstBody index =
      physicalChannel security r s secondComp secondAttach secondBody index := by
  have hrole (role : Fin r ⊕ Fin s) :
      roleChannel security r s firstComp firstAttach firstBody role =
        roleChannel security r s secondComp secondAttach secondBody role := by
    cases role with
    | inl index =>
      simp only [roleChannel, primaryChannel,
        averagedPairedChannel_periodic security _ _ _ _ (hcomp index) (hattach index)]
    | inr index =>
      simp only [roleChannel, ordinaryChannel, bodyChannel_periodic security _ _ (hbody index)]
  exact hrole (finSumFinEquiv.symm index)

theorem blockLaw_periodic (security : ℕ) (queue : ℤ) (first second : BlockIndex security → ℤ)
    (hequal : ∀ index, (first index : Root security) = (second index : Root security))
    (index : BlockIndex security) :
    TypedTaggedPhysical.blockLaw security queue first index = TypedTaggedPhysical.blockLaw security queue second index := by
  rcases index with leg | (center | point)
  · exact primaryLawAt_eq_of_cast security _ _ (hequal (.inl leg))
  · simp only [TypedTaggedPhysical.blockLaw, blockLawAt,
      shiftEquiv_eq_of_cast security _ _ (hequal (.inr (.inl center)))]
  · have hshift : ((first (.inr (.inr point)) + queue : ℤ) : Root security) =
        ((second (.inr (.inr point)) + queue : ℤ) : Root security) := by
      simp only [Int.cast_add, hequal]
    simp only [TypedTaggedPhysical.blockLaw, blockLawAt, shiftEquiv_eq_of_cast security _ _ hshift]

theorem selectedMass_periodic {security r s : ℕ} (selection : Selection security r s)
    (first second : BlockIndex security → ℤ)
    (hequal : ∀ index, (first index : Root security) = (second index : Root security))
    (kernel : DensityKernel (Primary := ActualControls.Palette security) (Body := ActualControls.SafePalette security) r s) :
    selectedMass selection first kernel = selectedMass selection second kernel := by
  unfold selectedMass jointMass
  congr 1
  funext index
  exact physicalChannel_periodic security r s _ _ _ _ _ _ (fun _ => hequal _) (fun _ => hequal _) (fun _ => hequal _) index

theorem conditionalMass_periodic {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (first second : BlockIndex security → ℤ)
    (hequal : ∀ index, (first index : Root security) = (second index : Root security))
    (kernel : DensityKernel (Primary := ActualControls.Palette security) (Body := ActualControls.SafePalette security) r s) :
    TypedTaggedPhysical.conditionalMass selection queue first kernel =
      TypedTaggedPhysical.conditionalMass selection queue second kernel := by
  unfold TypedTaggedPhysical.conditionalMass
  rw [selectedMass_periodic selection first second hequal]
  congr 1
  funext index
  exact blockLaw_periodic security queue first second hequal index.val

theorem conditionalPolynomial_periodic {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (first second : BlockIndex security → ℤ)
    (hequal : ∀ index, (first index : Root security) = (second index : Root security))
    (kernel : DensityKernel (Primary := ActualControls.Palette security) (Body := ActualControls.SafePalette security) r s) :
    conditionalPolynomial selection queue first kernel = conditionalPolynomial selection queue second kernel := by
  unfold conditionalPolynomial
  rw [conditionalMass_periodic selection queue first second hequal]

theorem conditionalPolynomial_residues {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (roots : BlockIndex security → ℤ)
    (kernel : DensityKernel (Primary := ActualControls.Palette security) (Body := ActualControls.SafePalette security) r s) :
    conditionalPolynomial selection queue roots kernel =
      conditionalPolynomial selection queue (fun block => ((roots block : Root security).val : ℤ)) kernel := by
  apply conditionalPolynomial_periodic
  intro index
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem conditionalMass_rootAt {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (layout : RoleIndex security ≃ BodyIndex security) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security)
    (kernel : DensityKernel (Primary := ActualControls.Palette security) (Body := ActualControls.SafePalette security) r s) :
    TypedTaggedPhysical.conditionalMass selection queue
      (fun block => rootAt security permutation latent (blockLayout layout block)) kernel =
      TaggedOutputFock.conditionalMass security r s selection layout queue permutation latent kernel := rfl

theorem conditionalPolynomial_rootAt {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (layout : RoleIndex security ≃ BodyIndex security) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security)
    (kernel : DensityKernel (Primary := ActualControls.Palette security) (Body := ActualControls.SafePalette security) r s) :
    conditionalPolynomial selection queue
      (fun block => rootAt security permutation latent (blockLayout layout block)) kernel =
      RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight
        (TaggedOutputFock.conditionalMass security r s selection layout queue permutation latent kernel) := rfl

end
end CurrentAFT.RootConditionalResidues

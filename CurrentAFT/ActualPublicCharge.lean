import CurrentAFT.PublicSignedOutput
import CurrentAFT.ProtectedChannel
import CurrentAFT.ActualPublicLegSeed

/-! # The source-independent public data needed for the actual charge test

The Fourier experiment conditions only on the score controls. Its positive
kernel has already averaged public anchor, blur, and baseline draws. Those
draws are made explicit here before any protected scalar or cycle is read.
-/
namespace CurrentAFT.ActualPublicCharge
open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy ActualBlockFock
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean PublicOutputExperiment
  PublicCoefficientOutput PublicSignedOutput
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  primaryLaw centerLaw safeLaw

abbrev Palette (security : ℕ) := FirstHistogram.Palette security

/-- This is the existing coarse endpoint kernel used in the Fourier
proof. Its public charge still requires the refinement below. -/
def mappedChannel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (controls : PublicWord security) :
    FiniteDist (Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)) :=
  (PublicSignedOutput.lawGiven security layout controls).map
    (fun word index => (ZMod.finEquiv (Parameters.modulus security)).toEquiv (word index))

abbrev LegCore (security : ℕ) := ActualPublicLegCharge.PublicSeed security × Palette security

/-- The public leg shift seed and its independent attachment baseline are
sampled without reading any protected scalar or closed-cycle latent. -/
def legCoreLaw (security : ℕ) : FiniteDist (LegCore security) :=
  (ActualPublicLegCharge.seedLaw security).prod (safeLaw security)

structure Core (security : ℕ) where
  controls : PublicWord security
  legs : Fin (Parameters.legCount security) → LegCore security
  queueBaselines : Fin (Parameters.modulus security) → Palette security
  bodyPermutation : Equiv.Perm (BodyIndex security)
  endpointPermutation : Equiv.Perm (Fin (Parameters.dimension security))

instance coreFintype (security : ℕ) : Fintype (Core security) := by
  classical
  let source := (((PublicWord security × (Fin (Parameters.legCount security) → LegCore security)) ×
    (Fin (Parameters.modulus security) → Palette security)) × Equiv.Perm (BodyIndex security)) ×
      Equiv.Perm (Fin (Parameters.dimension security))
  exact Fintype.ofEquiv source
    { toFun := fun draw => ⟨draw.1.1.1.1, draw.1.1.1.2, draw.1.1.2, draw.1.2, draw.2⟩
      invFun := fun core => ((((core.controls, core.legs), core.queueBaselines), core.bodyPermutation), core.endpointPermutation)
      left_inv := by rintro ⟨⟨⟨⟨controls, legs⟩, baselines⟩, body⟩, endpoints⟩; rfl
      right_inv := by intro core; cases core; rfl }

def proposal (security : ℕ) : FiniteDist (Core security) :=
  (((PublicOutputExperiment.reference security).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security))).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => safeLaw security)) |>.prod
      (FiniteDist.uniform (Equiv.Perm (BodyIndex security))) |>.prod
      (FiniteDist.uniform (Equiv.Perm (Fin (Parameters.dimension security))))).map
    (fun draw => ⟨draw.1.1.1.1, draw.1.1.1.2, draw.1.1.2, draw.1.2, draw.2⟩)

def pulledWeight (security order : ℕ) (coefficient : ActualControls.Coefficients security order)
    (core : Core security) : ℝ := actualWeight security order coefficient core.controls

/-- The fresh public coordinates conditional on the original score
controls; this law still contains no protected source sample. -/
def localSeedsLaw (security : ℕ) :
    FiniteDist ((Fin (Parameters.legCount security) → LegCore security) ×
      (Fin (Parameters.modulus security) → Palette security)) :=
  (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => safeLaw security))

def bodyPermutationLaw (security : ℕ) : FiniteDist (Equiv.Perm (BodyIndex security)) :=
  FiniteDist.uniform _

def endpointPermutationLaw (security : ℕ) : FiniteDist (Equiv.Perm (Fin (Parameters.dimension security))) :=
  FiniteDist.uniform _

def auxiliaryLaw (security : ℕ) (controls : PublicWord security) : FiniteDist (Core security) :=
  (((localSeedsLaw security).prod (bodyPermutationLaw security)).prod
      (endpointPermutationLaw security)).map
    (fun draw => ⟨controls, draw.1.1.1, draw.1.1.2, draw.1.2, draw.2⟩)

theorem auxiliary_expectation (security : ℕ) (controls : PublicWord security) (test : Core security → ℝ) :
    (auxiliaryLaw security controls).expectation test =
      (localSeedsLaw security).expectation (fun localSeeds =>
        (bodyPermutationLaw security).expectation (fun body =>
          (endpointPermutationLaw security).expectation (fun endpoints =>
            test ⟨controls, localSeeds.1, localSeeds.2, body, endpoints⟩))) := by
  unfold auxiliaryLaw
  simp only [FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_prod]

theorem proposal_expectation (security : ℕ) (test : Core security → ℝ) :
    (proposal security).expectation test =
      (PublicOutputExperiment.reference security).expectation
        (fun controls => (auxiliaryLaw security controls).expectation test) := by
  unfold proposal auxiliaryLaw localSeedsLaw bodyPermutationLaw endpointPermutationLaw
  simp only [FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_prod]

theorem proposal_weighted_channel {Output : Type*} [Fintype Output] (security : ℕ)
    (weight : PublicWord security → ℝ) (channel : Core security → FiniteDist Output) (output : Output) :
    (proposal security).expectation (fun core => weight core.controls * (channel core).weight output) =
      (PublicOutputExperiment.reference security).expectation (fun controls => weight controls *
        ((auxiliaryLaw security controls).mix channel).weight output) := by
  rw [proposal_expectation]
  apply congrArg (FiniteDist.expectation _)
  funext controls
  change (auxiliaryLaw security controls).expectation
    (fun core => weight core.controls * (channel core).weight output) =
      weight controls * (auxiliaryLaw security controls).expectation (fun core => (channel core).weight output)
  unfold auxiliaryLaw
  simp only [FiniteDist.expectation_map, Function.comp_def]
  exact FiniteDist.expectation_const_mul _ _ _

theorem proposal_controls (security : ℕ) (test : PublicWord security → ℝ) :
    (proposal security).expectation (fun core => test core.controls) =
      (PublicOutputExperiment.reference security).expectation test := by
  unfold proposal
  rw [FiniteDist.expectation_map]
  simp only [Function.comp_def, FiniteDist.expectation_prod, FiniteDist.expectation_const]

theorem pulledWeight_moment (security order power : ℕ) (coefficient : ActualControls.Coefficients security order)
    (scalar : ℝ) :
    (proposal security).expectation (fun core => |pulledWeight security order coefficient core - scalar| ^ power) =
      (PublicOutputExperiment.reference security).expectation
        (fun controls => |actualWeight security order coefficient controls - scalar| ^ power) :=
  proposal_controls security (fun controls => |actualWeight security order coefficient controls - scalar| ^ power)

theorem pulledWeight_mean (security order : ℕ) (coefficient : ActualControls.Coefficients security order) :
    (proposal security).expectation (pulledWeight security order coefficient) = coefficient.1 :=
  (proposal_controls security _).trans (actualWeight_mean security order coefficient)

theorem pulledWeight_clippingLoss (security order : ℕ) (coefficient : ActualControls.Coefficients security order) :
    clippingLoss (proposal security) (pulledWeight security order coefficient) =
      clippingLoss (PublicOutputExperiment.reference security) (actualWeight security order coefficient) :=
  proposal_controls security (fun controls => |actualWeight security order coefficient controls -
    clip (actualWeight security order coefficient controls)|)

def legShift (security : ℕ) (core : Core security) (leg : Fin (Parameters.legCount security)) : ℤ :=
  ActualPublicLegCharge.publicShift security (core.controls (.inl leg)).1 (core.legs leg).1

/-- The complete public numerator includes all body baselines and leg
shifts. It contains no protected source input. -/
def chargeValue (security : ℕ) (core : Core security) : ZMod (Parameters.modulus security) :=
  (∑ leg, ((core.controls (.inl leg)).2.val.val : ℤ)) +
    (∑ center, ((core.controls (.inr center)).2.val.val : ℤ)) +
    (∑ leg, ((core.legs leg).2.val : ℤ)) +
    (∑ point, ((core.queueBaselines point).val : ℤ)) +
    (∑ leg, legShift security core leg) - (Parameters.legCount security : ℤ)

def publicCharge (security : ℕ) (core : Core security) : Prop := chargeValue security core = 0

def attachmentPosition (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Fin (Parameters.legCount security) ↪ BodyIndex security where
  toFun leg := layout (.inr (.inr leg))
  inj' _first _second hequal := Sum.inr.inj (Sum.inr.inj (layout.injective hequal))

def queuePosition (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Fin (Parameters.modulus security) ↪ BodyIndex security where
  toFun point := layout (.inr (.inl point))
  inj' _first _second hequal := Sum.inl.inj (Sum.inr.inj (layout.injective hequal))

def queueSet (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) : Finset (BodyIndex security) :=
  Finset.univ.map (queuePosition security layout)

theorem queueSet_card (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    (queueSet security layout).card = Parameters.modulus security := by
  simp only [queueSet, Finset.card_map, Finset.card_univ, Fintype.card_fin]

def centerAt (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (vertex : BodyIndex security) : ℤ :=
  match layout.symm vertex with
  | .inl center => (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val.val
  | .inr (.inl point) => (core.queueBaselines point).val
  | .inr (.inr leg) => (core.legs leg).2.val

theorem sum_centerAt (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    (∑ vertex, centerAt security layout core vertex) =
      (∑ leg, ((core.controls (.inl leg)).2.val.val : ℤ)) +
      (∑ center, ((core.controls (.inr center)).2.val.val : ℤ)) +
      (∑ leg, ((core.legs leg).2.val : ℤ)) +
      (∑ point, ((core.queueBaselines point).val : ℤ)) := by
  unfold centerAt
  let value : RoleIndex security → ℤ := fun role => match role with
    | .inl center => ((core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val.val : ℤ)
    | .inr (.inl point) => ((core.queueBaselines point).val : ℤ)
    | .inr (.inr leg) => ((core.legs leg).2.val : ℤ)
  change (∑ vertex, value (layout.symm vertex)) = _
  rw [Equiv.sum_comp layout.symm value]
  dsimp only [value]
  simp only [Fintype.sum_sum_type]
  have hcontrol : (∑ center, ((core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val.val : ℤ)) =
      ∑ index : PublicIndex security, ((core.controls index).2.val.val : ℤ) := by
    convert Equiv.sum_comp (UniformTaggedOutput.centerSplit security).symm
      (fun index => ((core.controls index).2.val.val : ℤ)) using 1
  calc
    _ = (∑ index : PublicIndex security, ((core.controls index).2.val.val : ℤ)) +
        ((∑ point, ((core.queueBaselines point).val : ℤ)) +
          ∑ leg, ((core.legs leg).2.val : ℤ)) := by
      apply congrArg₂ (· + ·)
      · exact hcontrol
      · rfl
    _ = _ := by simp only [Fintype.sum_sum_type]; abel

theorem publicCharge_iff (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    PublicCharge.PublicChargeTest (Parameters.modulus security) (centerAt security layout core)
      (legShift security core) ↔ publicCharge security core := by
  unfold PublicCharge.PublicChargeTest publicCharge chargeValue
  rw [sum_centerAt]
  simp only [Fintype.card_fin, Int.cast_add, Int.cast_natCast, Int.cast_sum, sub_eq_zero]

private theorem eventMass_retype {State : Type*} {source : Fintype State} [target : Fintype State]
    (law : @FiniteDist State source) (event : State → Prop) :
    (FiniteDist.retype law).eventMass event = @FiniteDist.eventMass State source law event := by
  cases Subsingleton.elim source target
  rfl

theorem assembled_channel_charge {Seed : Type*} [Fintype Seed] (security : ℕ)
    (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) (seedLaw : FiniteDist Seed)
    (latent : Seed → BodyIndex security → ℤ) (second first : Seed → Fin (Parameters.legCount security) → ℤ)
    (scalar : Seed → ℤ)
    (relabel : Seed → Equiv.Perm (PublicCharge.EndpointIndex (Parameters.bodySize security) (Fin (Parameters.legCount security)))) :
    (FiniteDist.retype (protectedAssemblyChannel (Parameters.bodySize security) (Parameters.modulus security) seedLaw
      (centerAt security layout core) (legShift security core) latent (fun _ => core.bodyPermutation)
      (attachmentPosition security layout) second first (queueSet security layout) scalar relabel)).eventMass
        (fun endpoint => ∑ index, endpoint index = 0) = if publicCharge security core then 1 else 0 := by
  rw [eventMass_retype, protectedAssemblyChannel_charge _ _ seedLaw _ _ latent _ _ second first _
    (queueSet_card security layout) scalar relabel]
  simp only [publicCharge_iff security layout core]

end
end CurrentAFT.ActualPublicCharge

import CurrentAFT.ActualPublicCharge
import CurrentAFT.ActualPublicLegCharge
import CurrentAFT.FiniteChargeSupport

/-! # The actual positive channel at its complete public core -/
namespace CurrentAFT.RefinedPublicOutput
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge PositivePublicChannels
  PublicCoefficientOutput
open HistogramNormalization PhysicalSynthesis
open scoped BigOperators Classical
noncomputable section
local instance refinedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Residue (security : ℕ) := ZMod (Parameters.modulus security)

def embed (security : ℕ) (color : Palette security) : Residue security :=
  (ZMod.finEquiv (Parameters.modulus security)) color

theorem embed_shift (security : ℕ) (shift : ℤ) (color : Palette security) :
    embed security (shiftEquiv security shift color) = embed security color + (shift : Residue security) := by
  unfold embed shiftEquiv
  change (ZMod.finEquiv (Parameters.modulus security))
    ((ZMod.finEquiv (Parameters.modulus security)).symm
      ((ZMod.finEquiv (Parameters.modulus security)) color + (shift : Residue security))) = _
  exact RingEquiv.apply_symm_apply _ _

theorem embed_value (security : ℕ) (color : Palette security) :
    embed security color = (color.val : Residue security) :=
  ActualPublicLegCharge.finEquiv_natCast _ _

/-- The same protected scalar enters the actual pair and its attachment.
Only the anchor/blur seed and attachment baseline have become public. -/
def triple (security : ℕ) (root : ℤ) (primary : Palette security)
    (seed : LegCore security) : FiniteDist (Fin 3 → Palette security) :=
  (scalarLaw security).mix (fun scalar =>
    (ActualPublicLegCharge.refinedPair security primary scalar seed.1).map
      (fun pair => PhysicalBlockTensors.tripleEquiv.symm
        (pair, shiftEquiv security (root + scalar.val) seed.2)))

theorem triple_charge (security : ℕ) (root : ℤ) (primary : Palette security)
    (seed : LegCore security) :
    FiniteDist.HasValue (triple security root primary seed)
      (fun word => ∑ slot, embed security (word slot))
      (-1 + (ActualPublicLegCharge.publicShift security primary seed.1 : Residue security) +
        embed security seed.2 + (root : Residue security)) := by
  apply FiniteDist.HasValue.mix
  intro scalar
  apply FiniteDist.HasValue.map
  intro pair hpair
  change (∑ slot : Fin 3, embed security
    (PhysicalBlockTensors.tripleEquiv.symm
      (pair, shiftEquiv security (root + scalar.val) seed.2) slot)) = _
  rw [Fin.sum_univ_three]
  change embed security pair.1 + embed security pair.2 +
    embed security (shiftEquiv security (root + scalar.val) seed.2) = _
  have hcharge := ActualPublicLegCharge.refinedPair_modular_charge security primary scalar seed.1 pair hpair
  change embed security pair.1 + embed security pair.2 = _ at hcharge
  rw [hcharge, embed_shift, Int.cast_add]
  abel

def singleton (security : ℕ) (root : ℤ) (center : Palette security) :
    FiniteDist (Fin 1 → Palette security) :=
  (FixedPairedFirst.pointLaw security (shiftEquiv security root center)).map (fun color _ => color)

theorem singleton_charge (security : ℕ) (root : ℤ) (center : Palette security) :
    FiniteDist.HasValue (singleton security root center)
      (fun word => ∑ slot, embed security (word slot))
      (embed security center + (root : Residue security)) := by
  apply FiniteDist.HasValue.map
  intro color hcolor
  have hequal : color = shiftEquiv security root center := by
    rw [FixedPairedFirst.pointLaw_weight] at hcolor
    unfold FirstHistogram.atom at hcolor
    by_contra hne
    simp only [Ne.symm hne, if_false, ne_eq, not_true_eq_false] at hcolor
  subst color
  simpa only [Function.comp_apply, Fin.sum_univ_one] using embed_shift security root center

def blocks (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    (index : BlockIndex security) → FiniteDist (Slots security index → Palette security)
  | .inl leg => triple security (attachmentRoots security layout core.bodyPermutation latent leg)
      (core.controls (.inl leg)).1 (core.legs leg)
  | .inr (.inl center) => singleton security (centerRoots security layout core.bodyPermutation latent center)
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val
  | .inr (.inr point) => singleton security
      (queueRoots security layout core.bodyPermutation latent point + queue) (core.queueBaselines point)

def blockCharge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    BlockIndex security → Residue security
  | .inl leg => -1 + (legShift security core leg : Residue security) + embed security (core.legs leg).2 +
      (attachmentRoots security layout core.bodyPermutation latent leg : Residue security)
  | .inr (.inl center) => embed security
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val +
      (centerRoots security layout core.bodyPermutation latent center : Residue security)
  | .inr (.inr point) => embed security (core.queueBaselines point) +
      (queueRoots security layout core.bodyPermutation latent point : Residue security) + (queue : Residue security)

theorem blocks_charge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security)
    (index : BlockIndex security) :
    FiniteDist.HasValue (blocks security layout core queue latent index)
      (fun word => ∑ slot, embed security (word slot)) (blockCharge security layout core queue latent index) := by
  rcases index with leg | (center | point)
  · exact triple_charge security _ _ _
  · exact singleton_charge security _ _
  · simpa only [blockCharge, Int.cast_add, add_assoc] using
      singleton_charge security (queueRoots security layout core.bodyPermutation latent point + queue)
        (core.queueBaselines point)

theorem root_sum (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    (∑ center, centerRoots security layout permutation latent center) +
      ((∑ point, queueRoots security layout permutation latent point) +
        ∑ leg, attachmentRoots security layout permutation latent leg) = 0 := by
  have hsum := layout.sum_comp (fun position => rootAt security permutation latent position)
  simp only [Fintype.sum_sum_type] at hsum
  change _ = 0
  apply Eq.trans hsum
  unfold rootAt
  change (∑ position, PublicCharge.cycleDifference (fun vertex => (latent vertex).val)
    (permutation.symm position)) = 0
  rw [Equiv.sum_comp, PublicCharge.sum_cycleDifference]

theorem blockCharge_sum (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    (∑ index, blockCharge security layout core queue latent index) = chargeValue security core := by
  have hroot := congrArg (fun value : ℤ => (value : Residue security))
    (root_sum security layout core.bodyPermutation latent)
  have hcontrol : (∑ center,
      ((core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val.val : Residue security)) =
      ∑ index : PublicOutputExperiment.PublicIndex security, ((core.controls index).2.val.val : Residue security) := by
    convert Equiv.sum_comp (UniformTaggedOutput.centerSplit security).symm
      (fun index => ((core.controls index).2.val.val : Residue security)) using 1
  simp only [blockCharge, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, embed_value]
  simp only [Int.cast_add, Int.cast_sum, Int.cast_zero] at hroot
  have hq : (Parameters.modulus security : Residue security) = 0 := ZMod.natCast_self _
  rw [hq, zero_mul]
  unfold chargeValue
  simp only [Int.cast_sum, Int.cast_natCast]
  have hcontrol' := hcontrol
  simp only [Fintype.sum_sum_type] at hcontrol'
  linear_combination hroot + hcontrol'

def conditionalLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    FiniteDist (Sigma (Slots security) → Palette security) :=
  FiniteDist.retype (BlockProducts.blockLaw (Slots security) (blocks security layout core queue latent))

theorem conditionalLaw_charge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    FiniteDist.HasValue (conditionalLaw security layout core queue latent)
      (fun word => ∑ index, embed security (word index)) (chargeValue security core) := by
  have h := BlockProducts.blockLaw_has_sum (Slots security) (blocks security layout core queue latent)
    (embed security) (blockCharge security layout core queue latent) (blocks_charge security layout core queue latent)
  rw [blockCharge_sum] at h
  exact h

/-- The hidden scalar and complete latent cycle are sampled after the
full public core. Both public permutations were drawn in that core. -/
def lawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → Palette security) :=
  (scalarLaw security).mix (fun queue => (FiniteDist.retype (ActualFockBound.latentLaw security)).mix
    (fun latent => (conditionalLaw security layout core queue.val latent).map
      (fun word => AFT.relabel (renameWord (flatten security) word) core.endpointPermutation)))

def outputEquiv (security : ℕ) (permutation : Equiv.Perm (Fin (Parameters.dimension security))) :
    (Sigma (Slots security) → Palette security) ≃ (Fin (Parameters.dimension security) → Palette security) :=
  (renameWord (flatten security)).trans (AFT.relabelEquiv permutation)

theorem lawGiven_weight (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (word : Fin (Parameters.dimension security) → Palette security) :
    (lawGiven security layout core).weight word =
      (scalarLaw security).expectation (fun queue => (FiniteDist.retype (ActualFockBound.latentLaw security)).expectation
        (fun latent => (conditionalLaw security layout core queue.val latent).weight
          ((outputEquiv security core.endpointPermutation).symm word))) := by
  unfold lawGiven
  simp only [FiniteDist.mix_weight]
  apply Finset.sum_congr rfl
  intro queue _
  congr 1
  apply Finset.sum_congr rfl
  intro latent _
  congr 1
  change ((conditionalLaw security layout core queue.val latent).map
    (outputEquiv security core.endpointPermutation)).weight word = _
  exact FiniteDist.map_equiv_weight _ _ _

theorem lawGiven_charge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    FiniteDist.HasValue (lawGiven security layout core)
      (fun word => ∑ index, embed security (word index)) (chargeValue security core) := by
  apply FiniteDist.HasValue.mix
  intro queue
  apply FiniteDist.HasValue.mix
  intro latent
  apply FiniteDist.HasValue.map
  intro word hword
  change (∑ index, embed security (word ((flatten security).symm (core.endpointPermutation index)))) = _
  calc
    _ = ∑ index, embed security (word ((flatten security).symm index)) :=
      Equiv.sum_comp core.endpointPermutation (fun index => embed security (word ((flatten security).symm index)))
    _ = ∑ index, embed security (word index) :=
      Equiv.sum_comp (flatten security).symm (fun index => embed security (word index))
    _ = _ := conditionalLaw_charge security layout core queue.val latent word hword

def mappedChannel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → Residue security) :=
  (lawGiven security layout core).map (fun word index => embed security (word index))

theorem mappedChannel_charge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    (mappedChannel security layout core).eventMass (fun word => ∑ index, word index = 0) =
      if publicCharge security core then 1 else 0 := by
  have h : FiniteDist.HasValue (mappedChannel security layout core)
      (fun word => ∑ index, word index) (chargeValue security core) := by
    exact FiniteDist.HasValue.map _ _ _ _ (lawGiven_charge security layout core)
  exact FiniteDist.HasValue.eventMass_eq _ _ _ h (fun value => value = 0)

end
end CurrentAFT.RefinedPublicOutput

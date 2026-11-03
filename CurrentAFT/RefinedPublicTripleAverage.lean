import CurrentAFT.RefinedPublicOutput
import CurrentAFT.ActualPublicLegDisintegration

/-! # Exact coarse marginals of the public leg and baseline refinement -/
namespace CurrentAFT.RefinedPublicTripleAverage
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram FixedPairedFirst
  ActualBlockFock ActualPublicCharge RefinedPublicOutput PositivePublicChannels
open scoped BigOperators Classical
noncomputable section
local instance averageFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw centerLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

private theorem pair_map_triple_weight {Color : Type*} [Fintype Color]
    (law : FiniteDist (Color × Color)) (attached : Color) (word : Fin 3 → Color) :
    (law.map (fun pair => PhysicalBlockTensors.tripleEquiv.symm (pair, attached))).weight word =
      law.weight (word 0, word 1) * (if attached = word 2 then 1 else 0) := by
  rw [FiniteDist.map_weight]
  have hcondition (pair : Color × Color) :
      PhysicalBlockTensors.tripleEquiv.symm (pair, attached) = word ↔ pair = (word 0, word 1) ∧ attached = word 2 := by
    rw [Equiv.symm_apply_eq]
    change (pair, attached) = ((word 0, word 1), word 2) ↔ _
    simp only [Prod.mk.injEq]
  simp only [hcondition]
  by_cases hattached : attached = word 2
  · simp [hattached]
  · simp [hattached]

theorem triple_average (security : ℕ) (root : ℤ) (primary : Palette security) :
    (legCoreLaw security).mix (triple security root primary) = tripleGiven security root primary := by
  ext word
  rw [FiniteDist.mix_weight, tripleGiven_weight]
  simp only [triple, FiniteDist.mix_weight, pair_map_triple_weight]
  change (legCoreLaw security).expectation (fun core => (scalarLaw security).expectation
    (fun scalar => (ActualPublicLegCharge.refinedPair security primary scalar core.1).weight (word 0, word 1) *
      atom (shiftEquiv security (root + scalar.val) core.2) (word 2))) = _
  rw [FiniteDist.expectation_comm]
  apply congrArg (scalarLaw security).expectation
  funext scalar
  rw [legCoreLaw, FiniteDist.expectation_prod]
  simp_rw [FiniteDist.expectation_const_mul]
  rw [FiniteDist.expectation_mul_const]
  have hbase : (safeLaw security).expectation (fun center => atom (shiftEquiv security (root + scalar.val) center) (word 2)) =
      (attachmentAt security root scalar).weight (word 2) := by
    simp only [FiniteDist.expectation, attachmentAt, FiniteDist.map_weight, atom, mul_ite, mul_one, mul_zero]
  rw [hbase]
  congr 1
  change ((ActualPublicLegCharge.seedLaw security).mix (ActualPublicLegCharge.refinedPair security primary scalar)).weight (word 0, word 1) = _
  rw [ActualPublicLegCharge.pairAt_disintegration]

theorem singleton_average (security : ℕ) (root : ℤ) :
    (safeLaw security).mix (singleton security root) =
      singletonLaw ((safeLaw security).map (shiftEquiv security root)) := by
  ext word
  rw [FiniteDist.mix_weight, PositivePublicChannels.singletonLaw_weight]
  have hpoint (color : Palette security) :
      (singleton security root color).weight word = atom (shiftEquiv security root color) (word 0) := by
    change (singletonLaw (pointLaw security (shiftEquiv security root color))).weight word = _
    rw [PositivePublicChannels.singletonLaw_weight, pointLaw_weight]
    unfold atom
    split_ifs <;> rfl
  simp only [hpoint, FiniteDist.map_weight, atom, mul_ite, mul_one, mul_zero]

end
end CurrentAFT.RefinedPublicTripleAverage

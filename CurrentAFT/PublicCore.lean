import CurrentAFT.Conditioning

/-!
# Public-core conditioning before the hidden endpoint channel

At a fixed placement, the public core law is defined using only the public
proposal, its weight, and its public charge test. If the channel's endpoint
charge agrees almost surely with that public test, conditioning the public
core before applying the channel gives exactly the positive endpoint law.

The channel may retain arbitrary dependence among hidden coordinates. Its
charge consistency is an explicit interface to the construction's pointwise
assembly identity; this generic file does not assume or claim that the
actual assembly has already been connected to the channel.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Core Endpoint : Type*} [Fintype Core] [Fintype Endpoint]

private theorem event_atom_le (law : FiniteDist Endpoint) (event : Endpoint → Prop)
    (output : Endpoint) (houtput : event output) : law.weight output ≤ law.eventMass event := by
  unfold FiniteDist.eventMass
  calc
    _ = (if event output then law.weight output else 0) := by simp [houtput]
    _ ≤ ∑ point, if event point then law.weight point else 0 :=
      Finset.single_le_sum (f := fun point => if event point then law.weight point else 0)
        (fun point _ => by dsimp only; split_ifs; exact law.nonneg point; rfl)
        (Finset.mem_univ output)

private theorem eventMass_complement (law : FiniteDist Endpoint) (event : Endpoint → Prop) :
    law.eventMass (fun output => ¬event output) = 1 - law.eventMass event := by
  have hpartition : law.eventMass event + law.eventMass (fun output => ¬event output) = 1 := by
    unfold FiniteDist.eventMass
    rw [← Finset.sum_add_distrib]
    convert law.sum_one using 1
    apply Finset.sum_congr rfl
    intro output _
    by_cases houtput : event output <;> simp [houtput]
  linarith

/-- A zero-or-one conditional event mass gives pointwise restriction of the
kernel, including atoms of weight zero. -/
theorem channel_charge_restriction (law : FiniteDist Endpoint) (charge : Endpoint → Prop)
    (publicCharge : Prop)
    (hcharge : law.eventMass charge = if publicCharge then 1 else 0)
    (output : Endpoint) :
    (if charge output then law.weight output else 0) =
      if publicCharge then law.weight output else 0 := by
  by_cases hpublic : publicCharge
  · by_cases houtput : charge output
    · simp [hpublic, houtput]
    · have hmass : law.eventMass (fun output => ¬charge output) = 0 := by
        rw [eventMass_complement, hcharge, if_pos hpublic]
        ring
      have hzero : law.weight output = 0 :=
        le_antisymm ((event_atom_le law (fun output => ¬charge output) output houtput).trans_eq hmass)
          (law.nonneg output)
      simp [hpublic, houtput, hzero]
  · by_cases houtput : charge output
    · have hmass : law.eventMass charge = 0 := by simpa only [if_neg hpublic] using hcharge
      have hzero : law.weight output = 0 :=
        le_antisymm ((event_atom_le law charge output houtput).trans_eq hmass) (law.nonneg output)
      simp [hpublic, houtput, hzero]
    · simp [hpublic, houtput]

/-- The unnormalized public-core mass depends only on public core data. -/
def clippedPublicCoreWeight (proposal : FiniteDist Core) (weight : Core → ℝ)
    (publicCharge : Core → Prop) (core : Core) : ℝ :=
  if publicCharge core then proposal.weight core * clip (weight core) else 0

theorem clippedPublicCoreWeight_nonneg (proposal : FiniteDist Core) (weight : Core → ℝ)
    (publicCharge : Core → Prop) (core : Core) :
    0 ≤ clippedPublicCoreWeight proposal weight publicCharge core := by
  unfold clippedPublicCoreWeight
  split_ifs
  · exact mul_nonneg (proposal.nonneg core) (clip_nonneg _)
  · rfl

def publicCoreMass (proposal : FiniteDist Core) (weight : Core → ℝ)
    (publicCharge : Core → Prop) : ℝ :=
  ∑ core, clippedPublicCoreWeight proposal weight publicCharge core

/-- The positive public law is specified before any hidden-source channel.
Its arguments contain no hidden source, source sample, or output endpoint. -/
def positivePublicCoreLaw (proposal : FiniteDist Core) (weight : Core → ℝ)
    (publicCharge : Core → Prop) (hpositive : 0 < publicCoreMass proposal weight publicCharge) :
    FiniteDist Core :=
  FiniteDist.normalize (clippedPublicCoreWeight proposal weight publicCharge)
    (clippedPublicCoreWeight_nonneg proposal weight publicCharge) hpositive

/-- The public charge restriction can be moved through the same endpoint
channel exactly, before either measure is normalized. -/
theorem restricted_endpoint_eq_public_core (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (charge : Endpoint → Prop)
    (publicCharge : Core → Prop)
    (hcharge : ∀ core, (channel core).eventMass charge = if publicCharge core then 1 else 0)
    (output : Endpoint) :
    AFT.SignedConditioning.restricted
        (endpointMass proposal (fun core => clip (weight core)) channel) charge output =
      ∑ core, clippedPublicCoreWeight proposal weight publicCharge core *
        (channel core).weight output := by
  calc
    _ = ∑ core, proposal.weight core * clip (weight core) *
        (if charge output then (channel core).weight output else 0) := by
      by_cases houtput : charge output <;>
        simp [AFT.SignedConditioning.restricted, endpointMass, houtput]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro core _
      rw [channel_charge_restriction (channel core) charge (publicCharge core) (hcharge core)]
      by_cases hpublic : publicCharge core <;> simp [clippedPublicCoreWeight, hpublic]

/-- The endpoint charge mass equals the purely public acceptance numerator. -/
theorem chargedMass_eq_publicCoreMass (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (charge : Endpoint → Prop)
    (publicCharge : Core → Prop)
    (hcharge : ∀ core, (channel core).eventMass charge = if publicCharge core then 1 else 0) :
    chargedMass proposal weight channel charge = publicCoreMass proposal weight publicCharge := by
  unfold chargedMass
  simp_rw [restricted_endpoint_eq_public_core proposal weight channel charge publicCharge hcharge]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FiniteDist.sum_one, mul_one]
  rfl

/-- Conditioning public data before the hidden channel yields exactly the
endpoint-conditioned law used in the ambient-error argument. -/
theorem positivePublicCoreLaw_mix (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (charge : Endpoint → Prop)
    (publicCharge : Core → Prop)
    (hcharge : ∀ core, (channel core).eventMass charge = if publicCharge core then 1 else 0)
    (hpositive : 0 < publicCoreMass proposal weight publicCharge) :
    (positivePublicCoreLaw proposal weight publicCharge hpositive).mix channel =
      positiveEndpointLaw proposal weight channel charge
        (by rw [chargedMass_eq_publicCoreMass proposal weight channel charge publicCharge hcharge]
            exact hpositive) := by
  ext output
  change (∑ core, (clippedPublicCoreWeight proposal weight publicCharge core /
      publicCoreMass proposal weight publicCharge) * (channel core).weight output) =
    AFT.SignedConditioning.restricted
      (endpointMass proposal (fun core => clip (weight core)) channel) charge output /
        chargedMass proposal weight channel charge
  rw [restricted_endpoint_eq_public_core proposal weight channel charge publicCharge hcharge,
    chargedMass_eq_publicCoreMass proposal weight channel charge publicCharge hcharge,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro core _
  ring

/-- A placement is an explicit fixed parameter of the public law. This
definition never resamples placement inside its normalization. -/
def publicCoreLawAt {Placement : Type*} (placement : Placement)
    (proposal : Placement → FiniteDist Core) (weight : Placement → Core → ℝ)
    (publicCharge : Placement → Core → Prop)
    (hpositive : 0 < publicCoreMass (proposal placement) (weight placement) (publicCharge placement)) :
    FiniteDist Core :=
  positivePublicCoreLaw (proposal placement) (weight placement) (publicCharge placement) hpositive

theorem publicCoreLawAt_mix {Placement : Type*} (placement : Placement)
    (proposal : Placement → FiniteDist Core) (weight : Placement → Core → ℝ)
    (publicCharge : Placement → Core → Prop) (channel : Placement → Core → FiniteDist Endpoint)
    (charge : Endpoint → Prop)
    (hcharge : ∀ core, (channel placement core).eventMass charge =
      if publicCharge placement core then 1 else 0)
    (hpositive : 0 < publicCoreMass (proposal placement) (weight placement) (publicCharge placement)) :
    (publicCoreLawAt placement proposal weight publicCharge hpositive).mix (channel placement) =
      positiveEndpointLaw (proposal placement) (weight placement) (channel placement) charge
        (by rw [chargedMass_eq_publicCoreMass (proposal placement) (weight placement)
              (channel placement) charge (publicCharge placement) hcharge]
            exact hpositive) :=
  positivePublicCoreLaw_mix (proposal placement) (weight placement) (channel placement) charge
    (publicCharge placement) hcharge hpositive

/-- Pairing this public law with an independently drawn hidden source
preserves the hidden source marginal exactly. This formalizes the product
experiment; it does not assert an executable sampler or a runtime bound. -/
theorem publicCore_source_marginal {Source : Type*} [Fintype Source]
    (proposal : FiniteDist Core) (weight : Core → ℝ) (publicCharge : Core → Prop)
    (hpositive : 0 < publicCoreMass proposal weight publicCharge) (source : FiniteDist Source) :
    (((positivePublicCoreLaw proposal weight publicCharge hpositive).prod source).map Prod.snd) =
      source := by
  ext input
  simp only [FiniteDist.map_weight, Fintype.sum_prod_type, FiniteDist.prod_weight]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

end

end CurrentAFT

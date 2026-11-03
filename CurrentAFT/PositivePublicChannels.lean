import CurrentAFT.JointTaggedPhysicalFock
import AFT.WeightedPoolChannel

/-! # Literal positive public channels before coefficient weighting -/
namespace CurrentAFT.PositivePublicChannels
open AFT FirstHistogram DiffuseProfiles ProposalPrimary LocalReferenceEnergy FixedPairedFirst
  PairedReferenceEnergy TaggedPhysicalFock PhysicalSynthesis OrdinaryPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw

abbrev Palette (security : ℕ) := FirstHistogram.Palette security

/-- The actual positive leg conditioned on its public primary color. -/
def tripleGiven (security : ℕ) (root : ℤ) (primary : Palette security) : FiniteDist (Fin 3 → Palette security) :=
  (scalarLaw security).mix (fun scalar =>
    ((pairAt security primary scalar).prod (attachmentAt security root scalar)).map
      PhysicalBlockTensors.tripleEquiv.symm)

theorem tripleGiven_weight (security : ℕ) (root : ℤ) (primary : Palette security)
    (word : Fin 3 → Palette security) :
    (tripleGiven security root primary).weight word =
      (scalarLaw security).expectation (fun scalar => (pairAt security primary scalar).weight (word 0, word 1) *
        (attachmentAt security root scalar).weight (word 2)) := by
  simp only [tripleGiven, FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  rfl

theorem tripleGiven_average (security : ℕ) (root : ℤ) (word : Fin 3 → Palette security) :
    (primaryLaw security).expectation (fun primary => (tripleGiven security root primary).weight word) =
      (ActualBlockFock.primaryLawAt security root).weight word := by
  simp_rw [tripleGiven_weight]
  rw [FiniteDist.expectation_comm]
  unfold ActualBlockFock.primaryLawAt
  simp only [FiniteDist.mix_weight, FiniteDist.expectation,
    PositiveFirstCoefficient.positiveTripleLaw, PhysicalBlockTensors.sharedSourceTriple_weight,
    PhysicalBlockTensors.tripleMass, BlockDensity.attachedMass]
  apply Finset.sum_congr rfl
  intro scalar _
  congr 1
  apply Finset.sum_congr rfl
  intro primary _
  ring

/-- A single protected scalar supplies both the pair and its attachment.
The compensator is the prescribed public center, translated by its root. -/
def quadGiven (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (group : PhysicalSynthesis.Group security) : FiniteDist (Fin 4 → Palette security) :=
  (scalarLaw security).mix (fun scalar => fixedControlLaw security compensatorRoot attachmentRoot scalar group)

theorem quadGiven_weight (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (group : PhysicalSynthesis.Group security) (word : Fin 4 → Palette security) :
    (quadGiven security compensatorRoot attachmentRoot group).weight word =
      atom (shiftEquiv security compensatorRoot group.2) (word 0) *
        (tripleGiven security attachmentRoot group.1).weight (Fin.tail word) := by
  simp only [quadGiven, FiniteDist.mix_weight, fixedControlLaw_weight, controlMass,
    tripleGiven_weight, FiniteDist.expectation, Finset.mul_sum, Fin.tail]
  apply Finset.sum_congr rfl
  intro scalar _
  change (scalarLaw security).weight scalar * ((pairAt security group.1 scalar).weight (word 1, word 2) *
    (attachmentAt security attachmentRoot scalar).weight (word 3) *
      atom (shiftEquiv security compensatorRoot group.2) (word 0)) =
    atom (shiftEquiv security compensatorRoot group.2) (word 0) *
      ((scalarLaw security).weight scalar * ((pairAt security group.1 scalar).weight (word 1, word 2) *
        (attachmentAt security attachmentRoot scalar).weight (word 3)))
  ring

theorem quadGiven_average (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (word : Fin 4 → Palette security) :
    (groupLaw security).expectation (fun group =>
      (quadGiven security compensatorRoot attachmentRoot group).weight word) =
      (compensatorAt security compensatorRoot).weight (word 0) *
        (ActualBlockFock.primaryLawAt security attachmentRoot).weight (Fin.tail word) := by
  simp_rw [quadGiven_weight]
  rw [groupLaw, FiniteDist.expectation_prod]
  simp_rw [FiniteDist.expectation_mul_const]
  rw [FiniteDist.expectation_const_mul, tripleGiven_average, compensatorAt_channel]
  rfl

theorem paired_channel_public_sum (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : Palette security → ℝ) (word : Fin 4 → Palette security) :
    averagedPairedChannel security compensatorRoot attachmentRoot score word =
      (groupLaw security).expectation (fun group => pairedChannel security score group *
        (quadGiven security compensatorRoot attachmentRoot group).weight word) := by
  simp only [averagedPairedChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pairedMassLinear,
    LinearMap.coe_mk, AddHom.coe_mk, quadGiven, FiniteDist.mix_weight,
    fixedControlLaw_weight, FiniteDist.expectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro group _
  apply Finset.sum_congr rfl
  intro scalar _
  ring

/-- The ordinary channel is the actual public center followed by its
deterministic cyclic-root translation. -/
def bodyGiven (security : ℕ) (root : ℤ) (center : ActualControls.SafePalette security) :
    FiniteDist (Fin 1 → Palette security) :=
  (pointLaw security (shiftEquiv security root center.val)).map (fun color _ => color)

theorem singletonLaw_weight (security : ℕ) (law : FiniteDist (Palette security))
    (word : Fin 1 → Palette security) :
    (ActualBlockFock.singletonLaw law).weight word = law.weight (word 0) := by
  let equiv : Palette security ≃ (Fin 1 → Palette security) :=
    { toFun := fun color _ => color
      invFun := fun value => value 0
      left_inv := fun _ => rfl
      right_inv := fun value => funext (fun index => by have : index = 0 := Subsingleton.elim _ _; subst index; rfl) }
  change (law.map equiv).weight word = _
  rw [FiniteDist.map_equiv_weight]
  rfl

theorem bodyGiven_weight (security : ℕ) (root : ℤ) (center : ActualControls.SafePalette security)
    (word : Fin 1 → Palette security) :
    (bodyGiven security root center).weight word = atom (shiftEquiv security root center.val) (word 0) := by
  let equiv : Palette security ≃ (Fin 1 → Palette security) :=
    { toFun := fun color _ => color
      invFun := fun value => value 0
      left_inv := fun _ => rfl
      right_inv := fun value => funext (fun index => by have : index = 0 := Subsingleton.elim _ _; subst index; rfl) }
  change ((pointLaw security (shiftEquiv security root center.val)).map equiv).weight word = _
  rw [FiniteDist.map_equiv_weight, pointLaw_weight]
  simp only [equiv, Equiv.coe_fn_symm_mk, atom]
  split_ifs <;> rfl

theorem body_channel_public_sum (security : ℕ) (root : ℤ)
    (score : ActualControls.SafePalette security → ℝ) (word : Fin 1 → Palette security) :
    bodyChannel security root score word =
      (ActualControls.bodyReference security).expectation (fun center => score center *
        (bodyGiven security root center).weight word) := by
  simp_rw [bodyGiven_weight]
  simp_rw [show ∀ center : ActualControls.SafePalette security,
    score center = extendDensity security score center.val from fun center =>
      (extendDensity_safe security score center).symm]
  have href := SafeControlGroups.bodyReference_expectation security
    (fun color => extendDensity security score color * atom (shiftEquiv security root color) (word 0))
  apply Eq.trans ?_ href.symm
  change (centerLaw security).weight ((shiftEquiv security root).symm (word 0)) *
      extendDensity security score ((shiftEquiv security root).symm (word 0)) = _
  unfold FiniteDist.expectation atom
  have heq (color : Palette security) : (shiftEquiv security root color = word 0) ↔
      color = (shiftEquiv security root).symm (word 0) := Equiv.apply_eq_iff_eq_symm_apply _
  simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem bodyGiven_average (security : ℕ) (root : ℤ) (word : Fin 1 → Palette security) :
    (ActualControls.bodyReference security).expectation (fun center => (bodyGiven security root center).weight word) =
      (ActualBlockFock.singletonLaw (compensatorAt security root)).weight word := by
  simp_rw [bodyGiven_weight]
  rw [singletonLaw_weight, compensatorAt_channel]
  exact SafeControlGroups.bodyReference_expectation security
    (fun color => atom (shiftEquiv security root color) (word 0))

section FiniteTensor
variable {Index Input Control : Type*} [Fintype Index] [Fintype Input] [Fintype Control]
  [DecidableEq Index]

/-- Exact finite Fubini for an arbitrary joint input kernel. This identity
passes the joint kernel through the public response once, without a product
decomposition or a rank-dependent estimate. -/
theorem weighted_tensor_sum (law : Index → FiniteDist Control)
    (channel : Index → (Input → ℝ) →ₗ[ℝ] (Control → ℝ))
    (physical : Index → Control → ℝ) (kernel : (Index → Input) → ℝ) :
    (∑ input, kernel input * ∏ index,
      (law index).expectation (fun control =>
        channel index (Pi.single (input index) 1) control * physical index control)) =
    (FiniteDist.independent law).expectation (fun controls =>
      (∑ input, kernel input * ∏ index,
        channel index (Pi.single (input index) 1) (controls index)) *
      ∏ index, physical index (controls index)) := by
  unfold FiniteDist.expectation FiniteDist.independent
  simp_rw [← mul_assoc]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro controls _
  apply Finset.sum_congr rfl
  intro input _
  simp only [Finset.prod_mul_distrib]
  ring

end FiniteTensor
end
end CurrentAFT.PositivePublicChannels

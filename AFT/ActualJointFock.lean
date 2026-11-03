import AFT.ActualPrimaryFock
import AFT.JointPhysicalFock
import AFT.ReindexedFock

/-! # All actual primary and body channels on arbitrary joint canonical input -/
namespace AFT.V7Calibration
open Filter GaussianSource LocalTensors JointPhysicalChannel
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualJointFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualJointFockSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- A primary score changes its two endpoints, attached body and compensator;
a body score changes its single physical body output. -/
def actualRoleSlots : Bool → Type
  | true => Fin 4
  | false => Fin 1

instance actualRoleSlotsFintype (role : Bool) : Fintype (actualRoleSlots role) := by
  cases role <;> dsimp [actualRoleSlots] <;> infer_instance

def actualRoleInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (role : Bool) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  if role then actualPrimaryLaw cutoffScale parameter beta else actualBodyLaw cutoffScale parameter beta

def actualRoleChannel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue bodyShift : ℤ) :
    (role : Bool) → (Fin (Parameters.modulus parameter) → ℝ) →ₗ[ℝ]
      ((actualRoleSlots role → Fin (Parameters.modulus parameter)) → ℝ)
  | true => actualPairedDensityChannel cutoffScale parameter beta charts attachedRoot compensatorRoot queue
  | false => actualBodyDensityChannel cutoffScale parameter beta bodyShift

def actualRoleBound (parameter : ℕ) (role : Bool) : ℝ :=
  if role then Real.sqrt primaryFockEnergyConstant / (parameter : ℝ) ^ 15 else 16 / (parameter : ℝ) ^ 28

/-- Every role's literal output degree is at most four. -/
theorem actualRoleSlots_card_le (role : Bool) : Fintype.card (actualRoleSlots role) ≤ 4 := by
  cases role
  · change Fintype.card (Fin 1) ≤ 4
    norm_num
  · change Fintype.card (Fin 4) ≤ 4
    norm_num

/-- Complete arbitrary-joint-kernel Fock estimate for the actual V7 paired
and body channels. Every scalar bound is instantiated from the construction;
the only input condition is the kernel's canonicality. -/
theorem actual_joint_fock_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
        conditionalJointOutput cutoffScale parameter mark attached first second) ∧
      ∀ count : ℕ, ∀ role : Fin count → Bool, ∀ attachedRoot compensatorRoot queue bodyShift : Fin count → ℤ,
      (∀ index, |attachedRoot index| ≤ (v7RootCutoff parameter : ℤ)) →
      (∀ index, |compensatorRoot index| ≤ (v7RootCutoff parameter : ℤ)) →
      (∀ index, |queue index| ≤ (queueCutoff parameter : ℤ)) →
      (∀ index, |bodyShift index| ≤ (maxBodyShift cutoffScale parameter : ℤ)) →
      ∀ kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ,
      Hoeffding.Canonical (fun index => actualRoleInput cutoffScale parameter (beta parameter) (role index)) Finset.univ kernel →
      BlockProducts.taggedCoefficientEnergy (actualReferenceLaw cutoffScale parameter (beta parameter))
        (JointPhysicalChannel.mass (fun index => actualRoleSlots (role index))
          (fun index => actualRoleChannel cutoffScale parameter (beta parameter) charts
            (attachedRoot index) (compensatorRoot index) (queue index) (bodyShift index) (role index)) kernel)
        (Parameters.dimension parameter) ((parameter : ℝ) ^ 2) ≤
      ((Fintype.card (Sigma (fun index => actualRoleSlots (role index))) + 1 : ℕ) * (5 ^ count : ℕ) *
        ((count * 4).factorial : ℝ)) *
        ((∏ index, actualRoleBound parameter (role index) ^ 2) *
          (FiniteDist.independent (fun index => actualRoleInput cutoffScale parameter (beta parameter) (role index))).l2Sq kernel) := by
  filter_upwards [actual_primary_fock_energy_eventually cutoffScale hscale beta hbeta,
    actual_body_fock_energy_eventually cutoffScale hscale beta hbeta] with parameter hp hb
  obtain ⟨charts, hcharts, hprimary⟩ := hp
  refine ⟨charts, hcharts, ?_⟩
  intro count role ar cr queue shift har hcr hqueue hshift kernel hcanonical
  have hlocal (which : Bool) (attached compensator commonQueue bodyShift : ℤ)
      (ha : |attached| ≤ (v7RootCutoff parameter : ℤ))
      (hc : |compensator| ≤ (v7RootCutoff parameter : ℤ))
      (hq : |commonQueue| ≤ (queueCutoff parameter : ℤ))
      (hs : |bodyShift| ≤ (maxBodyShift cutoffScale parameter : ℤ))
      (density : Fin (Parameters.modulus parameter) → ℝ)
      (hd : (actualRoleInput cutoffScale parameter (beta parameter) which).expectation density = 0) :
      BlockProducts.taggedCoefficientEnergy (actualReferenceLaw cutoffScale parameter (beta parameter))
        (actualRoleChannel cutoffScale parameter (beta parameter) charts attached compensator commonQueue bodyShift which density)
        (Parameters.dimension parameter) ((parameter : ℝ) ^ 2) ≤
      actualRoleBound parameter which ^ 2 * (actualRoleInput cutoffScale parameter (beta parameter) which).l2Sq density := by
    cases which with
    | false =>
      change (actualBodyLaw cutoffScale parameter (beta parameter)).expectation density = 0 at hd
      have hh := hb density hd bodyShift hs
      change BlockProducts.taggedCoefficientEnergy _ (fun word : Fin 1 → Fin (Parameters.modulus parameter) =>
        actualBodySignedProfile cutoffScale parameter (beta parameter) density bodyShift (word 0)) _ _ ≤ _
      exact hh.trans_eq (by
        simp only [actualRoleBound, actualRoleInput, Bool.false_eq_true, if_false]
        ring)
    | true => exact hprimary attached compensator commonQueue ha hc hq density hd
  apply joint_mass_canonical_energy_le count (fun index => actualRoleSlots (role index))
    (actualReferenceLaw cutoffScale parameter (beta parameter)) 4
    (Parameters.dimension parameter) ((parameter : ℝ) ^ 2)
    (fun index => actualRoleSlots_card_le (role index))
    (fun index => actualRoleInput cutoffScale parameter (beta parameter) (role index))
    (fun index => actualRoleChannel cutoffScale parameter (beta parameter) charts
      (ar index) (cr index) (queue index) (shift index) (role index))
    (fun index => actualRoleBound parameter (role index)) _ kernel hcanonical
  intro index density hd
  exact hlocal (role index) (ar index) (cr index) (queue index) (shift index)
    (har index) (hcr index) (hqueue index) (hshift index) density hd

end
end AFT.V7Calibration

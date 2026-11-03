import CurrentAFT.ActualAffineCompletedOutput
import CurrentAFT.PublicCore
import AFT.FiniteRefresh

/-!
# Auxiliary activation refresh in the clipped and charged public law

This is a full-core identity.  It does not condition the Gaussian source on
activation.  The positive multiplier ignores activation bits, and their
fresh reference law can be integrated before applying the real public chart
completion.
-/

namespace CurrentAFT.AffineActivationFubini

open AFT AffineFlagCalibration ActualPublicCharge ActualPublicLegCharge
  ActualAffineCompletedOutput DiffuseProfiles ProposalPrimary LocalReferenceEnergy
  PublicOutputExperiment PublicAuxiliaryFubini ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Classical

noncomputable section

local instance activationFubiniFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance activationFubiniProdDecidableEq {A B : Type*} : DecidableEq (A × B) := Classical.decEq _
local instance activationPublicIndexDecidableEq (security : ℕ) : DecidableEq (PublicIndex security) :=
  @instDecidableEqSum _ _ (instDecidableEqFin _) (instDecidableEqFin _)
local instance activationBodyIndexDecidableEq (security : ℕ) : DecidableEq (BodyIndex security) :=
  instDecidableEqFin _
local instance activationEndpointIndexDecidableEq (security : ℕ) :
    DecidableEq (Fin (Parameters.dimension security)) := instDecidableEqFin _
local instance activationQueueIndexDecidableEq (security : ℕ) :
    DecidableEq (Fin (Parameters.modulus security)) := instDecidableEqFin _
local instance activationAnchorNonempty (security : ℕ) : Nonempty (InwardAnchor.Index security) :=
  ⟨⟨0, InwardAnchor.anchorWidth_pos security⟩⟩
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem independent_map_between {Index Input Output : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Input] [Fintype Output]
    (reference : Index → FiniteDist Input) (value : Index → Input → Output) :
    (FiniteDist.independent reference).map (fun word index => value index (word index)) =
      FiniteDist.independent (fun index => (reference index).map (value index)) := by
  ext target
  simp only [FiniteDist.map_weight, FiniteDist.independent]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.prod_ite_zero]
  have heq : (∀ index ∈ (Finset.univ : Finset Index), value index (word index) = target index) ↔
      (fun index => value index (word index)) = target := by
    simp only [Finset.mem_univ, forall_true_left, funext_iff]
  simp only [heq]

abbrev LegAux (security : ℕ) :=
  (Bool × (InwardAnchor.Index security × LocalReferenceEnergy.BlurSeed security)) ×
    AffineFlagCalibration.Palette security

def legAuxLaw (security : ℕ) : FiniteDist (LegAux security) :=
  ((FiniteDist.uniform Bool).prod
    ((FiniteDist.uniform (InwardAnchor.Index security)).prod (publicBlurLaw security))).prod (safeLaw security)

def joinLeg (security : ℕ) (flag : Bool) (aux : LegAux security) : LegCore security :=
  (⟨flag, aux.1.1, aux.1.2.1, aux.1.2.2⟩, aux.2)

theorem leg_expectation (security : ℕ) (test : LegCore security → ℝ) :
    (legCoreLaw security).expectation test =
      (activationLaw security).expectation (fun flag =>
        (legAuxLaw security).expectation (fun aux => test (joinLeg security flag aux))) := by
  unfold legCoreLaw seedLaw legAuxLaw
  simp only [FiniteDist.expectation_prod, FiniteDist.expectation_map, Function.comp_def]
  rfl

theorem leg_refresh_expectation (security : ℕ) (test : LegCore security → ℝ) :
    (legCoreLaw security).expectation (fun seed => (activationLaw security).expectation
      (fun flag => test (setMarked security seed.1 flag, seed.2))) =
        (legCoreLaw security).expectation test := by
  rw [leg_expectation, leg_expectation]
  change (activationLaw security).expectation (fun _ =>
    (legAuxLaw security).expectation (fun aux => (activationLaw security).expectation
      (fun flag => test (joinLeg security flag aux)))) = _
  rw [FiniteDist.expectation_const, FiniteDist.expectation_comm]

def legRefresh (security : ℕ) (seed : LegCore security) : FiniteDist (LegCore security) :=
  (activationLaw security).map (fun flag => (setMarked security seed.1 flag, seed.2))

theorem leg_refresh (security : ℕ) :
    (legCoreLaw security).mix (legRefresh security) = legCoreLaw security := by
  ext target
  have h := leg_refresh_expectation security
    (fun seed => if seed = target then (1 : ℝ) else 0)
  simp only [FiniteDist.expectation, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simpa only [FiniteDist.mix_weight, legRefresh, FiniteDist.map_weight] using h

def updateLegs (security : ℕ) (legs : Fin (Parameters.legCount security) → LegCore security)
    (bits : Fin (Parameters.legCount security) → Bool) :
    Fin (Parameters.legCount security) → LegCore security :=
  fun leg => (setMarked security (legs leg).1 (bits leg), (legs leg).2)

theorem legs_refresh (security : ℕ) :
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).mix
      (fun legs => (activationBitsLaw security).map (updateLegs security legs)) =
        FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security) := by
  have hk (legs : Fin (Parameters.legCount security) → LegCore security) :
      (activationBitsLaw security).map (updateLegs security legs) =
        FiniteDist.independent (fun leg => legRefresh security (legs leg)) :=
    independent_map_between (fun _ => activationLaw security)
      (fun leg flag => (setMarked security (legs leg).1 flag, (legs leg).2))
  simp_rw [hk]
  rw [CanonicalMoments.independent_mix]
  simp only [leg_refresh]

theorem legs_refresh_expectation (security : ℕ)
    (test : (Fin (Parameters.legCount security) → LegCore security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).expectation
      (fun legs => (activationBitsLaw security).expectation (fun bits => test (updateLegs security legs bits))) =
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).expectation test := by
  have h := congrArg (fun law => law.expectation test) (legs_refresh security)
  simp only [expectation_mix, FiniteDist.expectation_map, Function.comp_def] at h
  exact h

theorem legs_refresh_expectation_instance (security : ℕ)
    [decision : DecidableEq (Fin (Parameters.legCount security))]
    (test : (Fin (Parameters.legCount security) → LegCore security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).expectation
      (fun legs => (FiniteDist.retype (activationBitsLaw security)).expectation
        (fun bits => test (updateLegs security legs bits))) =
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).expectation test := by
  have hd : decision = activationFubiniFinDecidableEq (Parameters.legCount security) := Subsingleton.elim _ _
  cases hd
  simpa only [FiniteDist.expectation_retype] using legs_refresh_expectation security test

theorem proposal_refresh_expectation (security : ℕ) (test : Core security → ℝ) :
    (proposal security).expectation (fun core => (activationBitsLaw security).expectation
      (fun bits => test (setActivationBits security core bits))) =
        (proposal security).expectation test := by
  rw [proposal_expectation, proposal_expectation]
  apply congrArg (FiniteDist.expectation (PublicOutputExperiment.reference security))
  funext controls
  unfold auxiliaryLaw localSeedsLaw bodyPermutationLaw endpointPermutationLaw
  simp only [FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_prod]
  simp_rw [FiniteDist.expectation_comm
    (FiniteDist.uniform (Equiv.Perm (Fin (Parameters.dimension security)))) (activationBitsLaw security)]
  simp_rw [FiniteDist.expectation_comm
    (FiniteDist.uniform (Equiv.Perm (BodyIndex security))) (activationBitsLaw security)]
  simp_rw [FiniteDist.expectation_comm
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => safeLaw security))
      (activationBitsLaw security)]
  simpa only [FiniteDist.expectation_retype] using
    (@legs_refresh_expectation_instance security (instDecidableEqFin _) (fun legs =>
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => safeLaw security)).expectation (fun baselines =>
      (FiniteDist.uniform (Equiv.Perm (BodyIndex security))).expectation (fun body =>
        (FiniteDist.uniform (Equiv.Perm (Fin (Parameters.dimension security)))).expectation
          (fun endpoints => test ⟨controls, legs, baselines, body, endpoints⟩)))))

theorem weighted_refresh_expectation (security : ℕ) (multiplier test : Core security → ℝ)
    (hinvariant : ∀ core bits, multiplier (setActivationBits security core bits) = multiplier core) :
    (proposal security).expectation (fun core => multiplier core *
      (activationBitsLaw security).expectation (fun bits => test (setActivationBits security core bits))) =
        (proposal security).expectation (fun core => multiplier core * test core) := by
  calc
    _ = (proposal security).expectation (fun core => (activationBitsLaw security).expectation
        (fun bits => multiplier (setActivationBits security core bits) *
          test (setActivationBits security core bits))) := by
      apply congrArg (FiniteDist.expectation (proposal security))
      funext core
      rw [← FiniteDist.expectation_const_mul]
      apply congrArg (FiniteDist.expectation (activationBitsLaw security))
      funext bits
      rw [hinvariant]
    _ = _ := proposal_refresh_expectation security (fun core => multiplier core * test core)

local instance activationOutputEndpointDecidableEq (security : ℕ) :
    DecidableEq (Fin (Parameters.dimension security)) := Classical.decEq _

theorem positive_completed_output (security order : ℕ)
    (coefficient : ActualControls.Coefficients security order)
    (layout : RoleIndex security ≃ BodyIndex security)
    (word : Fin (Parameters.dimension security) → RefinedPublicOutput.Residue security) :
    (proposal security).expectation (fun core => positiveMultiplier security order coefficient core *
      (ActualAffineCompletedOutput.mappedChannel security layout core).weight word) =
    (proposal security).expectation (fun core => positiveMultiplier security order coefficient core *
      (RefinedPublicOutput.mappedChannel security layout core).weight word) := by
  have h := weighted_refresh_expectation security (positiveMultiplier security order coefficient)
    (fun core => (RefinedPublicOutput.mappedChannel security layout core).weight word)
    (positiveMultiplier_setActivationBits security order coefficient)
  apply Eq.trans _ h
  apply congrArg (FiniteDist.expectation (proposal security))
  funext core
  apply congrArg (fun x : ℝ => positiveMultiplier security order coefficient core * x)
  exact congrArg (fun law => law.weight word) (mapped_activation_average security layout core).symm

/-- The normalized clipped and charged public law can be followed by the
real source-independent chart completion, with exactly the refined output
law already used in the Fourier/conditioning proof. -/
theorem positive_core_completed_output (security order : ℕ)
    (coefficient : ActualControls.Coefficients security order)
    (layout : RoleIndex security ≃ BodyIndex security)
    (hpositive : 0 < publicCoreMass (proposal security) (pulledWeight security order coefficient)
      (publicCharge security)) :
    (positivePublicCoreLaw (proposal security) (pulledWeight security order coefficient)
      (publicCharge security) hpositive).mix (ActualAffineCompletedOutput.mappedChannel security layout) =
    (positivePublicCoreLaw (proposal security) (pulledWeight security order coefficient)
      (publicCharge security) hpositive).mix (RefinedPublicOutput.mappedChannel security layout) := by
  ext word
  simp only [FiniteDist.mix_weight, positivePublicCoreLaw, FiniteDist.normalize,
    div_mul_eq_mul_div, ← Finset.sum_div]
  apply congrArg (fun numerator : ℝ => numerator /
    ∑ core, clippedPublicCoreWeight (proposal security) (pulledWeight security order coefficient)
      (publicCharge security) core)
  have hw (core : Core security) :
      clippedPublicCoreWeight (proposal security) (pulledWeight security order coefficient)
        (publicCharge security) core =
      (proposal security).weight core * positiveMultiplier security order coefficient core := by
    unfold clippedPublicCoreWeight positiveMultiplier
    split_ifs <;> ring
  simp_rw [hw]
  simpa only [FiniteDist.expectation, mul_assoc] using
    positive_completed_output security order coefficient layout word

end
end CurrentAFT.AffineActivationFubini

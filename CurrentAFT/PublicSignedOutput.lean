import CurrentAFT.PublicCoefficientOutput
import CurrentAFT.ActualPhysicalTail
import CurrentAFT.ActualMixedMassFormula

/-! # The actual public weight and the final signed endpoint experiment -/
namespace CurrentAFT.PublicSignedOutput
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean PublicOutputExperiment PublicCoefficientOutput HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool primaryLaw centerLaw

/-- One common queue scalar and one independent uniform whole-body
permutation are used for all local factors of this positive public kernel. -/
def rawLawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (controls : PublicWord security) : FiniteDist (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) :=
  (FiniteDist.retype (ActualWeightedFourier.randomizationLaw security)).mix (fun sample =>
    (outputLawGiven security layout sample.1.val sample.2 controls).map (renameWord (flatten security)))

/-- The final independent endpoint permutation is a genuine finite positive
sampler. The public controls remain unchanged. -/
def lawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (controls : PublicWord security) : FiniteDist (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) :=
  AFT.symmetrize (rawLawGiven security layout controls)

/-- The original coefficientWeight is evaluated on public controls before
the entire protected source and the two permutation draws. -/
def signedMass (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order)
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) : ℝ :=
  (reference security).expectation (fun controls => actualWeight security order coefficient controls *
    (lawGiven security layout controls).weight word)

theorem signedMass_sum (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order) :
    (∑ word, signedMass security order layout coefficient word) = coefficient.1 := by
  unfold signedMass FiniteDist.expectation
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.mul_sum, FiniteDist.sum_one, mul_one]
  exact actualWeight_mean security order coefficient

theorem signedMass_symmetrized (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order) :
    signedMass security order layout coefficient = symmetrizedMass
      (fun word => (reference security).expectation (fun controls => actualWeight security order coefficient controls *
        (rawLawGiven security layout controls).weight word)) := by
  funext word
  unfold signedMass lawGiven
  simp_rw [sampler_symmetrize_weight]
  rw [SymmetrizedOutputRename.average]
  simp_rw [SymmetrizedOutputRename.smul]

theorem raw_weighted_mass (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order)
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) :
    (reference security).expectation (fun controls => actualWeight security order coefficient controls *
      (rawLawGiven security layout controls).weight word) =
      (FiniteDist.retype (ActualWeightedFourier.randomizationLaw security)).expectation (fun sample =>
        weightedPhysicalMass security order layout sample.1.val sample.2 coefficient (word ∘ flatten security)) := by
  unfold rawLawGiven
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  change (reference security).expectation (fun controls => actualWeight security order coefficient controls *
    (FiniteDist.retype (ActualWeightedFourier.randomizationLaw security)).expectation (fun sample =>
      (outputLawGiven security layout sample.1.val sample.2 controls).weight (word ∘ flatten security))) = _
  simp_rw [← FiniteDist.expectation_const_mul]
  exact FiniteDist.expectation_comm _ _ _

/-- The original coefficientWeight, integrated against the actual positive
public experiment, is exactly the complete constructed mass used by the
all-frequency physical Fock and Fourier bounds. -/
theorem signedMass_eq_signedOutputMass (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (coefficient : ActualControls.Coefficients security order) :
    signedMass security order layout coefficient =
      ActualWeightedFourier.signedOutputMass security order hroom layout coefficient := by
  rw [signedMass_symmetrized]
  simp_rw [raw_weighted_mass]
  conv_lhs => rw [SymmetrizedOutputRename.average]
  unfold ActualWeightedFourier.signedOutputMass
  have hmixed : ActualWeightedFourier.mixedMass security order hroom layout coefficient =
      fun word => (FiniteDist.retype (ActualWeightedFourier.randomizationLaw security)).expectation (fun sample =>
        CoefficientOutputFock.familyMass security order hroom layout sample.1.val sample.2 coefficient word) := by
    funext word
    exact ActualWeightedFourier.mixedMass_retype_formula security order hroom layout coefficient word
  rw [hmixed]
  conv_rhs => rw [SymmetrizedOutputRename.average]
  funext word
  apply congrArg (FiniteDist.expectation _)
  funext sample
  have hphysical : (fun output => weightedPhysicalMass security order layout sample.1.val sample.2 coefficient
      (output ∘ flatten security)) = renamedMass (flatten security)
        (physicalFamilyMass security order hroom layout sample.1.val sample.2 coefficient) := by
    funext output
    exact weightedPhysicalMass_eq security order hroom layout sample.1.val sample.2 coefficient (output ∘ flatten security)
  rw [hphysical]
  exact congrFun (symmetrized_physicalFamily_eq security order hroom layout sample.1.val sample.2 coefficient) word

section Rates
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq

theorem current_public_fock_eventually (order : ℕ) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ _hroom : 2 * order ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∀ coefficient : ActualControls.Coefficients security order,
      ActualFockBound.energy (LocalReferenceEnergy.uniformReference security)
        (signedMass security order layout coefficient) (BackgroundRates.radius security) ≤
        (CoefficientOutputFock.normConstant order 1 * ControlNorm.coefficientNorm (primaryLaw security)
          (ActualControls.bodyReference security) order (BackgroundRates.primaryFactor security)
          (BackgroundRates.bodyFactor security) coefficient) ^ 2 := by
  obtain ⟨threshold, hthreshold⟩ := ActualWeightedFourier.current_signed_fock_eventually order
  refine ⟨threshold, ?_⟩
  intro security hsecurity hroom layout coefficient
  rw [signedMass_eq_signedOutputMass security order hroom layout coefficient]
  exact hthreshold security hsecurity hroom layout coefficient

theorem current_public_weighted_fourier_eventually (order : ℕ) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ _hroom : 2 * order ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∀ coefficient : ActualControls.Coefficients security order,
      weightedSupportEnergy Finset.univ
        (fun frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security) =>
          (FrequencySupport.support frequency).card)
        (fun frequency => ‖FourierCoordinates.fourier (ZMod.finEquiv (Parameters.modulus security)).toEquiv
          (fun word => (signedMass security order layout coefficient word : ℂ)) frequency‖ ^ 2)
        (ActualPhysicalTail.analysisRadius security) ≤
        (CoefficientOutputFock.normConstant order 1 * ControlNorm.coefficientNorm (primaryLaw security)
          (ActualControls.bodyReference security) order (BackgroundRates.primaryFactor security)
          (BackgroundRates.bodyFactor security) coefficient) ^ 2 := by
  obtain ⟨threshold, hthreshold⟩ := ActualWeightedFourier.current_complete_weighted_fourier_eventually order
  refine ⟨threshold, ?_⟩
  intro security hsecurity hroom layout coefficient
  rw [signedMass_eq_signedOutputMass security order hroom layout coefficient]
  exact hthreshold security hsecurity hroom layout coefficient

def coefficient (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (input : ActualControls.Coefficients security order)
    (frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)) : ℂ :=
  FourierCoordinates.fourier (ZMod.finEquiv (Parameters.modulus security)).toEquiv
    (fun word => (signedMass security order layout input word : ℂ)) frequency

theorem coefficient_eq (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (input : ActualControls.Coefficients security order)
    (frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)) :
    coefficient security order layout input frequency = ActualPhysicalTail.coefficient security order hroom layout input frequency := by
  unfold coefficient ActualPhysicalTail.coefficient
  rw [signedMass_eq_signedOutputMass security order hroom layout input]

/-- Complete nonzero-frequency tail for the literal public experiment.
Only the exact calibration equations remain as a premise. -/
theorem current_public_tail_eventually (order : ℕ) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ _hroom : 2 * order ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∀ input : ActualControls.Coefficients security order,
      (∀ frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security),
        frequency ≠ 0 → (FrequencySupport.support frequency).card ≤ order →
          coefficient security order layout input frequency = 0) →
      (∑ frequency ∈ Finset.univ.erase (0 : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)),
        ‖coefficient security order layout input frequency‖ ^ 2) ≤
      (CoefficientOutputFock.normConstant order 1 * ControlNorm.coefficientNorm (primaryLaw security)
        (ActualControls.bodyReference security) order (BackgroundRates.primaryFactor security)
        (BackgroundRates.bodyFactor security) input) ^ 2 /
          ActualPhysicalTail.analysisRadius security ^ (2 * (order + 1)) := by
  obtain ⟨threshold, hthreshold⟩ := ActualPhysicalTail.current_complete_tail_eventually order
  refine ⟨threshold, ?_⟩
  intro security hsecurity hroom layout input hcancel
  have h := hthreshold security hsecurity hroom layout input (fun frequency hnonzero hsmall => by
    rw [← coefficient_eq security order hroom layout input frequency]
    exact hcancel frequency hnonzero hsmall)
  simpa only [coefficient_eq security order hroom layout input] using h

end Rates

end
end CurrentAFT.PublicSignedOutput

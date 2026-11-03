import CurrentAFT.ActualCalibrationSolution
import CurrentAFT.ActualLayouts
import CurrentAFT.PublicLowDegree

/-! # Complete Fourier energy for the actual stable calibration solution -/
namespace CurrentAFT.ActualCalibrationFourier
open AFT ActualCompleteStability ActualLayouts ConditionalHistogramMean ActualCycleMeanMGF
  BackgroundRates ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def calibratedCoefficients (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security) (layout : RoleIndex security ≃ BodyIndex security) :
    ActualControls.Coefficients security order :=
  coefficients security order horder hsecurity (blockLayout layout)

def energyBudget (order : ℕ) : ℝ := (2 * CoefficientOutputFock.normConstant order 1)^2

theorem energyBudget_nonneg (order : ℕ) : 0 ≤ energyBudget order := sq_nonneg _

theorem norm_budget (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security) (layout : RoleIndex security ≃ BodyIndex security) :
    (CoefficientOutputFock.normConstant order 1 * coefficientNorm (ProposalPrimary.primaryLaw security)
      (ActualControls.bodyReference security) order (primaryFactor security) (bodyFactor security)
      (calibratedCoefficients security order horder hsecurity layout))^2 ≤ energyBudget order := by
  have hnorm := coefficients_norm security order horder hsecurity (blockLayout layout)
  have hnonneg := coefficientNorm_nonneg (ProposalPrimary.primaryLaw security)
    (ActualControls.bodyReference security) order (primaryFactor security) (bodyFactor security)
    (RaisingPatternBudget.primaryFactor_pos security).le (RaisingPatternBudget.bodyFactor_pos security).le
    (calibratedCoefficients security order horder hsecurity layout)
  have hc := CoefficientOutputFock.normConstant_nonneg order 1
  have hbound := mul_le_mul_of_nonneg_left hnorm hc
  change _ ≤ (2 * CoefficientOutputFock.normConstant order 1)^2
  apply pow_le_pow_left₀ (mul_nonneg hc hnonneg)
  simpa only [mul_comm] using hbound

theorem full_fock_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff, ∀ hsecurity : threshold order horder ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ActualFockBound.energy (LocalReferenceEnergy.uniformReference security)
        (PublicSignedOutput.signedMass security order layout
          (calibratedCoefficients security order horder hsecurity layout)) (radius security) ≤ energyBudget order := by
  obtain ⟨cutoff, hcutoff⟩ := PublicSignedOutput.current_public_fock_eventually order
  refine ⟨cutoff, ?_⟩
  intro security hlarge hsecurity layout
  exact (hcutoff security hlarge (room security order horder hsecurity) layout _).trans
    (norm_budget security order horder hsecurity layout)

theorem full_weighted_fourier_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff, ∀ hsecurity : threshold order horder ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      weightedSupportEnergy Finset.univ
        (fun frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security) =>
          (FrequencySupport.support frequency).card)
        (fun frequency => ‖PublicSignedOutput.coefficient security order layout
          (calibratedCoefficients security order horder hsecurity layout) frequency‖^2)
        (ActualPhysicalTail.analysisRadius security) ≤ energyBudget order := by
  obtain ⟨cutoff, hcutoff⟩ := PublicSignedOutput.current_public_weighted_fourier_eventually order
  refine ⟨cutoff, ?_⟩
  intro security hlarge hsecurity layout
  exact (hcutoff security hlarge (room security order horder hsecurity) layout _).trans
    (norm_budget security order horder hsecurity layout)

/-- Only the final identification of the complete physical PGF is a premise.
The actual coefficient norm and the full energy estimate have been discharged. -/
theorem tail_of_physical_calibration_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff, ∀ hsecurity : threshold order horder ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight
          (ActualWeightedFourier.mixedMass security order (room security order horder hsecurity) layout
            (calibratedCoefficients security order horder hsecurity layout))) = 1 →
      (∑ frequency ∈ Finset.univ.erase (0 : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)),
        ‖PublicSignedOutput.coefficient security order layout
          (calibratedCoefficients security order horder hsecurity layout) frequency‖^2) ≤
            energyBudget order / ActualPhysicalTail.analysisRadius security^(2 * (order + 1)) := by
  obtain ⟨cutoff, hcutoff⟩ := PublicLowDegree.complete_tail_of_calibration_eventually order
  refine ⟨cutoff, ?_⟩
  intro security hlarge hsecurity layout hcalibrated
  exact (hcutoff security hlarge (room security order horder hsecurity) layout _ hcalibrated).trans
    (div_le_div_of_nonneg_right (norm_budget security order horder hsecurity layout)
      (pow_nonneg (div_nonneg (PhysicalFockRates.radius_nonneg security) (Real.sqrt_nonneg _)) _))

end
end CurrentAFT.ActualCalibrationFourier

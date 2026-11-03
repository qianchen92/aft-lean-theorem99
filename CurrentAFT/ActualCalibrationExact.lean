import CurrentAFT.ActualCompletePGF
import CurrentAFT.ActualCalibratedPublic

/-! # Exact physical calibration and the actual positive protected law

All response, Fourier, moment and charge estimates are proved for the
constructed weight. No physical-calibration premise remains in this file.
The finite positive law is not a finite-bit sampler or an unprotected
Gaussian affine-transport theorem.
-/
namespace CurrentAFT.ActualCalibrationExact
open AFT ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
  ActualCompletePhysical ActualLayouts ConditionalHistogramMean ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance exactFinDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem calibrated (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security) (layout : RoleIndex security ≃ BodyIndex security) :
    ActualCalibratedPublic.Calibrated security order horder hsecurity layout := by
  have h := fullResponse_physical security order horder (room security order horder hsecurity) layout
    (solution security order horder hsecurity (blockLayout layout))
  rw [solution_response, map_one] at h
  exact h

theorem coefficient_zero (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security) (layout : RoleIndex security ≃ BodyIndex security)
    (frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security))
    (hnonzero : frequency ≠ 0) (hdegree : (FrequencySupport.support frequency).card ≤ order) :
    PublicSignedOutput.coefficient security order layout
      (calibratedCoefficients security order horder hsecurity layout) frequency = 0 :=
  PublicLowDegree.coefficient_zero security order (room security order horder hsecurity) layout _
    (calibrated security order horder hsecurity layout) frequency hnonzero hdegree

theorem complete_tail_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff, ∀ hsecurity : threshold order horder ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      (∑ frequency ∈ Finset.univ.erase (0 : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)),
        ‖PublicSignedOutput.coefficient security order layout
          (calibratedCoefficients security order horder hsecurity layout) frequency‖^2) ≤
            energyBudget order / ActualPhysicalTail.analysisRadius security^(2 * (order + 1)) := by
  obtain ⟨cutoff, hcutoff⟩ := tail_of_physical_calibration_eventually order horder
  exact ⟨cutoff, fun security hlarge hsecurity layout =>
    hcutoff security hlarge hsecurity layout (calibrated security order horder hsecurity layout)⟩

/-- Every fixed accuracy order has the actual positive, source-independent
public law at every fixed placement, with the proved inverse-power error. -/
theorem positive_protected_eventually (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ActualCalibratedPublic.PositiveConclusion security (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) hsecurity layout (inversePower security accuracyOrder) := by
  obtain ⟨cutoff, hcutoff⟩ := ActualCalibratedPublic.negligible_eventually accuracyOrder
  exact ⟨cutoff, fun security hlarge hsecurity layout => hcutoff security hlarge hsecurity layout
    (calibrated security _ _ hsecurity layout)⟩

/-- The stability threshold is part of the chosen security cutoff, rather
than an additional unproved assumption on the positive construction. -/
theorem positive_protected_exists (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∃ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ActualCalibratedPublic.PositiveConclusion security (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) hsecurity layout (inversePower security accuracyOrder) := by
  obtain ⟨cutoff, hcutoff⟩ := positive_protected_eventually accuracyOrder
  refine ⟨max cutoff (threshold _ (calibrationOrder_at_least_two accuracyOrder)), ?_⟩
  intro security hlarge layout
  have hs := (le_max_right _ _).trans hlarge
  exact ⟨hs, hcutoff security ((le_max_left _ _).trans hlarge) hs layout⟩

end
end CurrentAFT.ActualCalibrationExact

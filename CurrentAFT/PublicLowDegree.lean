import CurrentAFT.PublicSignedOutput
import CurrentAFT.LowDegreeCancellation
import CurrentAFT.CenteredPolynomialSymmetry

/-! # Exact cancellation and the full tail for the literal public experiment -/
namespace CurrentAFT.PublicLowDegree
open AFT RepresentedPolynomial ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean
  FourierCoordinates FrequencySupport
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem support_positive_of_ne_zero {Index : Type*} [Fintype Index] {modulus : ℕ}
    (frequency : Index → ZMod modulus) (hnonzero : frequency ≠ 0) : 0 < (support frequency).card := by
  by_contra hpositive
  have hempty : support frequency = ∅ := Finset.card_eq_zero.mp (by omega)
  apply hnonzero
  funext index
  by_contra hneq
  have hmem : index ∈ support frequency := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩
  rw [hempty] at hmem
  simp only [Finset.notMem_empty] at hmem

/-- Calibration is imposed on the actual shared-queue, body-permuted
physical mass before the independent final endpoint permutation. -/
theorem coefficient_zero (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (input : ActualControls.Coefficients security order)
    (hcalibrated : TruncatedOutput.quotientMap order
      (centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight
        (ActualWeightedFourier.mixedMass security order hroom layout input)) = 1)
    (frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security))
    (hnonzero : frequency ≠ 0) (hdegree : (support frequency).card ≤ order) :
    PublicSignedOutput.coefficient security order layout input frequency = 0 := by
  unfold PublicSignedOutput.coefficient
  rw [PublicSignedOutput.signedMass_eq_signedOutputMass security order hroom layout input]
  apply LowDegreeCancellation.fourier_zero_of_calibrated
    (ZMod.finEquiv (Parameters.modulus security)).toEquiv _
    (HistogramNormalization.symmetrizedMass_exchangeable _) order _ frequency
    (support_positive_of_ne_zero frequency hnonzero) hdegree
  rw [CenteredPolynomialSymmetry.symmetrized]
  exact hcalibrated

theorem complete_tail_of_calibration_eventually (order : ℕ) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ hroom : 2 * order ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security, ∀ input : ActualControls.Coefficients security order,
      TruncatedOutput.quotientMap order
        (centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight
          (ActualWeightedFourier.mixedMass security order hroom layout input)) = 1 →
      (∑ frequency ∈ Finset.univ.erase (0 : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)),
        ‖PublicSignedOutput.coefficient security order layout input frequency‖ ^ 2) ≤
      (CoefficientOutputFock.normConstant order 1 * ControlNorm.coefficientNorm (ProposalPrimary.primaryLaw security)
        (ActualControls.bodyReference security) order (BackgroundRates.primaryFactor security)
        (BackgroundRates.bodyFactor security) input) ^ 2 /
          ActualPhysicalTail.analysisRadius security ^ (2 * (order + 1)) := by
  obtain ⟨threshold, hthreshold⟩ := PublicSignedOutput.current_public_tail_eventually order
  refine ⟨threshold, ?_⟩
  intro security hsecurity hroom layout input hcalibrated
  exact hthreshold security hsecurity hroom layout input
    (fun frequency hnonzero hdegree => coefficient_zero security order hroom layout input hcalibrated frequency hnonzero hdegree)

end
end CurrentAFT.PublicLowDegree

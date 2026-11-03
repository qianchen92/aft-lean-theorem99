import CurrentAFT.PublicAffinePipelineLaw
import CurrentAFT.NumericalGaussianAccuracy

/-! Closing the actual public sampling and emission stages from a certified
calibration-table producer. Only the producer's weight approximation remains
an input to this composition lemma. -/
namespace CurrentAFT.PublicAffinePipeline
open AFT ActualPublicCharge ActualCompleteStability ActualGaussianAccuracy ActualCalibrationRates
open Filter
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current

theorem accuracy_eventually (accuracyOrder : ℕ)
    (producer : ∀ security, Producer security (Parameters.calibrationOrder accuracyOrder))
    (weightError : ℕ → ℝ) (hnonneg : ∀ security, 0 ≤ weightError security) (hnegligible : Negligible weightError)
    (hweight : ∀ᶠ security : ℕ in atTop,
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ (layout : CurrentLayoutDraw.Cache security) (core : Core security),
        |(BinaryPublicRejection.coreWeight security security (Parameters.calibrationOrder accuracyOrder)
          (producer security layout).value core : ℝ)-
          ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout.layout core| ≤ weightError security) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      (fairGaussian security (Parameters.calibrationOrder accuracyOrder) (producer security)).totalVariation
        (CurrentZeroFiber.uniformFiber security) ≤ (security : ℝ)^(-(accuracyOrder : ℝ)) := by
  have herror := CurrentMaterializedCompletion.totalError_negligible hnegligible
  obtain ⟨analyticCutoff, ha⟩ := NumericalGaussianAccuracy.gaussian_with_numerics accuracyOrder
    (fun security => CurrentMaterializedCompletion.totalError security (weightError security)) herror
  have hall : ∀ᶠ security : ℕ in atTop,
      analyticCutoff ≤ security ∧ 1 ≤ security ∧
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ (layout : CurrentLayoutDraw.Cache security) (core : Core security),
        |(BinaryPublicRejection.coreWeight security security (Parameters.calibrationOrder accuracyOrder)
          (producer security layout).value core : ℝ)-
          ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout.layout core| ≤ weightError security := by
    filter_upwards [eventually_ge_atTop analyticCutoff, eventually_ge_atTop 1, hweight] with security hc hs hw
    exact ⟨hc,hs,hw⟩
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp hall
  refine ⟨cutoff, fun security hs => ?_⟩
  obtain ⟨hc, hsec, hw⟩ := hcutoff security hs
  obtain ⟨hsecurity, hbound⟩ := ha security hc
  apply gaussian_accuracy
  intro layout
  obtain ⟨hpositive, hmass, htotal⟩ := hbound layout.layout
  rw [fixedGaussian_eq]
  have hlower : 1/(4*(Parameters.modulus security : ℝ)) ≤ 1/(2*(Parameters.modulus security : ℝ)) := by
    have hq : (0 : ℝ)<Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.pos
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h := CurrentMaterializedCompletion.gaussian_error security (Parameters.calibrationOrder accuracyOrder) hsec
    layout.layout (producer security layout).value
    (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
      (calibrationOrder_at_least_two accuracyOrder) hsecurity layout.layout)
    (weightError security) _ (hnonneg security) (hw hsecurity layout) hpositive (hlower.trans hmass) le_rfl
  exact h.trans htotal

end
end CurrentAFT.PublicAffinePipeline

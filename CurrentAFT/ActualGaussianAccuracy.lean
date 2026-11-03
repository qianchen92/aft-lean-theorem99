import CurrentAFT.ActualGaussianAffine

/-! # Fixed-order accuracy of the actual ideal affine law

The calibration order is exactly `4 * accuracyOrder + 267`. All analytical
premises are discharged. This ideal finite law still requires the separately
developed finite-bit implementation before it is a uniform PPT sampler.
-/
namespace CurrentAFT.ActualGaussianAccuracy
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineTransport CurrentPublicAffineSample CurrentZeroFiber
  ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
  ActualCalibrationClipping ActualGaussianAffine
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩
local instance dimensionNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by rw [← LobsterCoordinates.current_vertex_count security]; omega⟩⟩

theorem gaussian_bound_eventually (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
          (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∃ hpositive : 0 < publicCoreMass (proposal security)
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security),
        1 / (2 * (Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security)
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security) ∧
        (gaussianLaw security layout
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) hpositive).totalVariation
          (uniformFiber security) ≤
            2 * (Parameters.modulus security : ℝ) *
              (fourierError security (Parameters.calibrationOrder accuracyOrder) +
                loss security (Parameters.calibrationOrder accuracyOrder)
                  (calibrationOrder_at_least_two accuracyOrder) hsecurity (ActualLayouts.blockLayout layout)) +
              CurrentSourceProtection.budget security := by
  obtain ⟨cutoff, hcutoff⟩ := ActualCalibratedPublic.positive_eventually accuracyOrder
  refine ⟨cutoff, ?_⟩
  intro security hlarge hsecurity layout
  obtain ⟨hpositive, hlower, herror⟩ := hcutoff security hlarge hsecurity layout
    (ActualCalibrationExact.calibrated security _ _ hsecurity layout)
  refine ⟨hpositive, hlower, ?_⟩
  apply gaussian_fiber_bound
  unfold ActualCalibratedPublic.weight
  rw [protectedEndpoint_eq_calibrated]
  exact herror

private theorem five_inversePower (security order : ℕ) (hsecurity : 3 ≤ security) :
    4 * inversePower security (order + 2) + 1 / (security : ℝ)^(order + 2) ≤
      1 / (security : ℝ)^order := by
  have hs : (3 : ℝ) ≤ security := by exact_mod_cast hsecurity
  have hspos : (0 : ℝ) < security := by linarith
  have hb : (security : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show security ≤ Parameters.base security by unfold Parameters.base; omega)
  have hi : inversePower security (order + 2) ≤ 1 / (security : ℝ)^(order + 2) :=
    one_div_le_one_div_of_le (pow_pos hspos _) (pow_le_pow_left₀ hspos.le hb _)
  calc
    _ ≤ 4 * (1 / (security : ℝ)^(order + 2)) + 1 / (security : ℝ)^(order + 2) := by
      linarith only [hi]
    _ = 5 / (security : ℝ)^(order + 2) := by ring
    _ ≤ _ := by
      rw [pow_add]
      apply (div_le_div_iff₀ (mul_pos (pow_pos hspos _) (pow_pos hspos _)) (pow_pos hspos _)).mpr
      have hsq : (5 : ℝ) ≤ (security : ℝ)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg hspos.le order)]

/-- The ideal law attains the manuscript's requested precision with its
specified calibration order, uniformly over every fixed public placement. -/
theorem gaussian_accuracy_exists (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∃ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
          (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∃ hpositive : 0 < publicCoreMass (proposal security)
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security),
        1 / (2 * (Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security)
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security) ∧
        (gaussianLaw security layout
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) hpositive).totalVariation
          (uniformFiber security) ≤ (security : ℝ)^(-(accuracyOrder : ℝ)) := by
  obtain ⟨positiveCutoff, hpositive⟩ := gaussian_bound_eventually accuracyOrder
  obtain ⟨clipCutoff, hclip⟩ := charged_loss_negligible (Parameters.calibrationOrder accuracyOrder)
    (calibrationOrder_at_least_two accuracyOrder) (accuracyOrder + 2)
  have hall : ∀ᶠ security : ℕ in atTop,
      positiveCutoff ≤ security ∧ clipCutoff ≤ security ∧
      threshold (Parameters.calibrationOrder accuracyOrder) (calibrationOrder_at_least_two accuracyOrder) ≤ security ∧
      3 ≤ security ∧ (Parameters.modulus security : ℝ) *
        fourierError security (Parameters.calibrationOrder accuracyOrder) ≤ inversePower security (accuracyOrder + 2) ∧
      |CurrentSourceProtection.budget security| ≤ 1 / (security : ℝ)^(accuracyOrder + 2) := by
    filter_upwards [eventually_ge_atTop positiveCutoff, eventually_ge_atTop clipCutoff,
      eventually_ge_atTop (threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder)), eventually_ge_atTop 3,
      charged_fourier_eventually accuracyOrder, CurrentSourceTail.budget_negligible (accuracyOrder + 2)]
      with security hp hc ht hs hf hb
    exact ⟨hp, hc, ht, hs, hf, hb⟩
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp hall
  refine ⟨cutoff, ?_⟩
  intro security hlarge
  obtain ⟨hp, hc, ht, hs, hf, hb⟩ := hcutoff security hlarge
  refine ⟨ht, ?_⟩
  intro layout
  obtain ⟨hcore, hlower, hbound⟩ := hpositive security hp ht layout
  have hloss := hclip security hc ht (ActualLayouts.blockLayout layout)
  have hbudget := (le_abs_self (CurrentSourceProtection.budget security)).trans hb
  refine ⟨hcore, hlower, hbound.trans ?_⟩
  calc
    _ ≤ 4 * inversePower security (accuracyOrder + 2) + 1 / (security : ℝ)^(accuracyOrder + 2) := by
      nlinarith only [hf, hloss, hbudget]
    _ ≤ 1 / (security : ℝ)^accuracyOrder := five_inversePower security accuracyOrder hs
    _ = _ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      simp only [one_div]

end
end CurrentAFT.ActualGaussianAccuracy

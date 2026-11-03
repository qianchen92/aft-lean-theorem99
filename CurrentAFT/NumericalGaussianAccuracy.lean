import CurrentAFT.ActualGaussianAccuracy
import CurrentAFT.CurrentMaterializedCompletionLaw

/-! Numerical implementation error fits the existing calibration order.
The proof retains the spare two inverse powers in the analytic estimate;
it never raises the manuscript's order `4*a+267`. -/
namespace CurrentAFT.NumericalGaussianAccuracy
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineTransport CurrentPublicAffineSample CurrentZeroFiber
  ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
  ActualCalibrationClipping ActualGaussianAccuracy
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem six_inversePower (security order : ℕ) (hsecurity : 3  ≤  security) :
    4*inversePower security (order+2)+2/(security : ℝ)^(order+2)  ≤  1/(security : ℝ)^order := by
  have hs : (3 : ℝ) ≤ security := by exact_mod_cast hsecurity
  have hspos : (0 : ℝ)<security := by linarith
  have hb : (security : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show security ≤ Parameters.base security by unfold Parameters.base; omega)
  have hi : inversePower security (order+2) ≤ 1/(security : ℝ)^(order+2) :=
    one_div_le_one_div_of_le (pow_pos hspos _) (pow_le_pow_left₀ hspos.le hb _)
  calc
    _ ≤ 4*(1/(security : ℝ)^(order+2))+2/(security : ℝ)^(order+2) := by linarith only [hi]
    _ = 6/(security : ℝ)^(order+2) := by ring
    _  ≤  _ := by
      rw [pow_add]
      apply (div_le_div_iff₀ (mul_pos (pow_pos hspos _) (pow_pos hspos _)) (pow_pos hspos _)).mpr
      have hsq : (6 : ℝ) ≤ (security : ℝ)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg hspos.le order)]

theorem gaussian_with_numerics (accuracyOrder : ℕ) (extra : ℕ → ℝ) (hextra : Negligible extra) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∃ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∃ hpositive : 0<publicCoreMass (proposal security)
        (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
          (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security),
        1/(2*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security)
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security) ∧
        (gaussianLaw security layout
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) hpositive).totalVariation
          (uniformFiber security)+extra security  ≤  (security : ℝ)^(-(accuracyOrder : ℝ)) := by
  obtain ⟨positiveCutoff, hpositive⟩ := gaussian_bound_eventually accuracyOrder
  obtain ⟨clipCutoff, hclip⟩ := charged_loss_negligible (Parameters.calibrationOrder accuracyOrder)
    (calibrationOrder_at_least_two accuracyOrder) (accuracyOrder+2)
  have hall : ∀ᶠ security : ℕ in atTop,
      positiveCutoff ≤ security ∧ clipCutoff ≤ security ∧
      threshold (Parameters.calibrationOrder accuracyOrder) (calibrationOrder_at_least_two accuracyOrder) ≤ security ∧
      3 ≤ security ∧ (Parameters.modulus security : ℝ)*
        fourierError security (Parameters.calibrationOrder accuracyOrder) ≤ inversePower security (accuracyOrder+2) ∧
      |CurrentSourceProtection.budget security| ≤ 1/(security : ℝ)^(accuracyOrder+2) ∧
      |extra security| ≤ 1/(security : ℝ)^(accuracyOrder+2) := by
    filter_upwards [eventually_ge_atTop positiveCutoff, eventually_ge_atTop clipCutoff,
      eventually_ge_atTop (threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder)), eventually_ge_atTop 3,
      charged_fourier_eventually accuracyOrder, CurrentSourceTail.budget_negligible (accuracyOrder+2),
      hextra (accuracyOrder+2)] with security hp hc ht hs hf hb he
    exact ⟨hp, hc, ht, hs, hf, hb, he⟩
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp hall
  refine ⟨cutoff, ?_⟩
  intro security hlarge
  obtain ⟨hp, hc, ht, hs, hf, hb, he⟩ := hcutoff security hlarge
  refine ⟨ht, ?_⟩
  intro layout
  obtain ⟨hcore, hlower, hbound⟩ := hpositive security hp ht layout
  have hloss := hclip security hc ht (ActualLayouts.blockLayout layout)
  have hbudget := (le_abs_self (CurrentSourceProtection.budget security)).trans hb
  have hnum := (le_abs_self (extra security)).trans he
  refine ⟨hcore, hlower, ?_⟩
  calc
    _  ≤  4*inversePower security (accuracyOrder+2)+2/(security : ℝ)^(accuracyOrder+2) := by
      rw [show 2/(security : ℝ)^(accuracyOrder+2) = 2*(1/(security : ℝ)^(accuracyOrder+2)) by ring]
      nlinarith only [hf, hloss, hbudget, hbound, hnum]
    _  ≤  1/(security : ℝ)^accuracyOrder := six_inversePower security accuracyOrder hs
    _ = _ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      simp only [one_div]

end
end CurrentAFT.NumericalGaussianAccuracy

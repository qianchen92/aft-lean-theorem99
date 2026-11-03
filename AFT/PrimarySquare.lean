import AFT.PrimarySup
import AFT.PrimaryL1

/-! # The actual calibrated primary has the sharp counting-square budget -/

namespace AFT

open scoped BigOperators Classical

/-- Near-uniform total variation and point height control the counting square
through the centered profile. The uniform contribution is kept exactly. -/
theorem probability_counting_square_le {Color : Type*} [Fintype Color]
    (profile : Color → ℝ) (hnonneg : ∀ color, 0 ≤ profile color) (hmass : ∑ color, profile color = 1)
    (hcard : 0 < Fintype.card Color) (height : ℝ) (hheight : ∀ color, profile color ≤ height) :
    (∑ color, profile color ^ 2) ≤ 1 / (Fintype.card Color : ℝ) +
      (height + 1 / (Fintype.card Color : ℝ)) *
        ∑ color, |profile color - 1 / (Fintype.card Color : ℝ)| := by
  have hn : (0 : ℝ) < Fintype.card Color := by exact_mod_cast hcard
  let uniform : ℝ := 1 / Fintype.card Color
  have hu : 0 ≤ uniform := by dsimp [uniform]; positivity
  have hcenter : (∑ color, (profile color - uniform) ^ 2) = (∑ color, profile color ^ 2) - uniform := by
    have heq (color) : (profile color - uniform) ^ 2 = profile color ^ 2 - 2 * uniform * profile color + uniform ^ 2 := by ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass,
      Finset.sum_const, nsmul_eq_mul]
    dsimp [uniform]
    field_simp
    ring
  have hpoint (color : Color) : (profile color - uniform) ^ 2 ≤ (height + uniform) * |profile color - uniform| := by
    have ha : |profile color - uniform| ≤ height + uniform :=
      (abs_sub (profile color) uniform).trans (by rw [abs_of_nonneg (hnonneg color), abs_of_nonneg hu]; linarith [hheight color])
    have hh := mul_le_mul_of_nonneg_right ha (abs_nonneg (profile color - uniform))
    nlinarith [sq_abs (profile color - uniform)]
  have hsum := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)
  rw [hcenter, ← Finset.mul_sum] at hsum
  linarith

namespace V7Calibration

open Filter GaussianSource
open scoped Topology

/-- Both inverse-activation gains remain in the actual primary counting
square. This is the physical endpoint budget before replacing activation by
its proven sharp V7 lower bound. -/
theorem actual_primary_counting_square_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∑ color, actualPrimary cutoffScale parameter (beta parameter) color ^ 2) ≤
        1 / (Parameters.modulus parameter : ℝ) +
          (3 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 10) +
            1 / (Parameters.modulus parameter : ℝ)) *
              (192 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8)) := by
  filter_upwards [actual_primary_upper_eventually cutoffScale hscale beta hbeta,
    actual_primary_uniform_l1_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta] with parameter hmax hl hp
  have hq := (Parameters.modulus_prime parameter).pos
  have h := probability_counting_square_le (actualPrimary cutoffScale parameter (beta parameter))
    (fun color => (hp.1 color).le) hp.2 (by simpa using hq) _ hmax
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply add_le_add le_rfl
  have ha0 : 0 ≤ 3 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 10) :=
    (hp.1 ⟨0, hq⟩).le.trans (hmax ⟨0, hq⟩)
  exact mul_le_mul_of_nonneg_left hl.1 (by positivity)

/-- The two inverse-activation factors cancel against the actual squared
mark amplitude. The resulting local physical square cost is `O(λ⁻¹⁸)`. -/
theorem actual_marked_primary_square_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (v7Activation cutoffScale parameter) ^ 2 *
        (∑ color, actualPrimary cutoffScale parameter (beta parameter) color ^ 2) ≤
          769 / (parameter : ℝ) ^ 18 := by
  filter_upwards [actual_primary_counting_square_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hs hp
  let activation := v7Activation cutoffScale parameter
  let q : ℝ := Parameters.modulus parameter
  let x : ℝ := parameter
  have hx : 0 < x := by dsimp only [x]; exact_mod_cast (by omega : 0 < parameter)
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast (by omega : 1 ≤ parameter)
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have ha : 0 < activation := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have ha1 : activation ≤ 1 := activation_le_one _ _ _ _
  have ha2 : activation ^ 2 ≤ 1 := by nlinarith
  have hqx : x ^ 40 ≤ q := by
    dsimp only [x, q]
    exact_mod_cast (show parameter ^ 40 ≤ Parameters.modulus parameter by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
  have hq18 : x ^ 18 ≤ q := (pow_le_pow_right₀ hx1 (by norm_num : 18 ≤ 40)).trans hqx
  have hq8 : x ^ 18 ≤ q * x ^ 8 := hq18.trans (le_mul_of_one_le_right hq.le (one_le_pow₀ hx1))
  have h1 : activation ^ 2 / q ≤ 1 / x ^ 18 :=
    (div_le_div_of_nonneg_right ha2 hq.le).trans
      (one_div_le_one_div_of_le (by positivity) hq18)
  have h2 : 192 * activation / (q * x ^ 8) ≤ 192 / x ^ 18 := by
    calc
      _ ≤ 192 / (q * x ^ 8) := div_le_div_of_nonneg_right (by linarith only [ha1]) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) hq8
  have h := mul_le_mul_of_nonneg_left hs (sq_nonneg activation)
  have heq : activation ^ 2 * (1 / q + (3 / (activation * x ^ 10) + 1 / q) * (192 / (activation * x ^ 8))) =
      activation ^ 2 / q + 576 / x ^ 18 + 192 * activation / (q * x ^ 8) := by
    field_simp
    ring
  change _ ≤ activation ^ 2 * (1 / q + (3 / (activation * x ^ 10) + 1 / q) * (192 / (activation * x ^ 8))) at h
  rw [heq] at h
  change _ ≤ 769 / x ^ 18
  calc
    _ ≤ 1 / x ^ 18 + 576 / x ^ 18 + 192 / x ^ 18 :=
      h.trans (add_le_add (add_le_add h1 le_rfl) h2)
    _ = _ := by ring

end V7Calibration

end AFT

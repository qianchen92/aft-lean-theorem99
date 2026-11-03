import AFT.ActualPairMarginals
import AFT.InactivePairCanonical

/-! # The actual active-minus-inactive endpoint law before its covariance -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology
noncomputable section

def activeEndpointDifference (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  actualMarkedPair cutoffScale parameter beta first second - averagedInactivePair cutoffScale parameter first second

def activeEndpointDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  activeEndpointDifference cutoffScale parameter beta first second /
    (actualPrimary cutoffScale parameter beta first * actualPrimary cutoffScale parameter beta second)

/-- The full pair norm is of order sqrt(q/A), while the fixed fibers
retain the full q/A height. The activation coefficient is not discarded. -/
theorem actual_active_endpoint_density_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      let p := actualPrimary cutoffScale parameter (beta parameter)
      let D := activeEndpointDensity cutoffScale parameter (beta parameter)
      (∑ first, ∑ second, activeEndpointDifference cutoffScale parameter (beta parameter) first second) = 0 ∧
      (∀ first second, |D first second| ≤ 36 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) ∧
      (∑ first, ∑ second, p first * p second * D first second^2) ≤
        72 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ∧
      (∀ first, (∑ second, p second * D first second^2) ≤
        (36 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter)^2) ∧
      (∀ second, (∑ first, p first * D first second^2) ≤
        (36 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter)^2) := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [actual_inactive_pair_bounds_eventually cutoffScale hscale,
    actual_full_anchor_safe_eventually cutoffScale hscale,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
      (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
      (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel]
    with parameter hi ha hp hl
  dsimp only at hl ⊢
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let marked := actualMarkedPair cutoffScale parameter (beta parameter)
  let inactive := averagedInactivePair cutoffScale parameter
  let D := activeEndpointDensity cutoffScale parameter (beta parameter)
  let q : ℝ := Parameters.modulus parameter
  let width : ℝ := Parameters.anchorWidth parameter
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hw : 0 < width := by
    dsimp only [width, Parameters.anchorWidth]
    exact_mod_cast pow_pos (show 0 < Parameters.security parameter by have := Parameters.security_ge_two parameter; omega) 32
  have hp0 (color) : 0 < p color := hp.1 color
  have hpp (x y) : 0 < p x*p y := mul_pos (hp0 x) (hp0 y)
  have hmean := averagedInactivePair_bounds cutoffScale parameter hi
  have hImass : (∑ x, ∑ y, inactive x y) = 1 := hmean.2.1
  have hm0 (x y) : 0 ≤ marked x y := mul_nonneg (hp0 x).le (blurredAnchorKernel_nonneg _ _ _ _ _ _)
  have hmass : (∑ x, ∑ y, marked x y) = 1 := by
    simp only [marked, actualMarkedPair, ← Finset.mul_sum, (ha _).1, mul_one]
    exact hp.2
  have hmarked (x y) : marked x y / (p x*p y) ≤ 4*q/width := by
    have heq : marked x y / (p x*p y) =
        blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
          (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) x y.val / p y := by
      dsimp only [marked, actualMarkedPair]
      change p x * _ / (p x * p y) = _
      field_simp [ne_of_gt (hp0 x), ne_of_gt (hp0 y)]
    rw [heq]
    calc
      _ ≤ width⁻¹ / p y := div_le_div_of_nonneg_right (blurredAnchorKernel_le _ _ _ _ _ _) (hp0 y).le
      _ ≤ width⁻¹ / (1/(4*q)) := div_le_div_of_nonneg_left (by positivity) (by positivity) (hl.1 y)
      _ = _ := by field_simp
  have hinactive (x y) : inactive x y / (p x*p y) ≤ 32*q/width := by
    calc
      _ ≤ (2/(width*q)) / (p x*p y) := div_le_div_of_nonneg_right (hmean.2.2 x y) (hpp x y).le
      _ ≤ (2/(width*q)) / (1/(4*q))^2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have hh := mul_le_mul (hl.1 x) (hl.1 y) (by positivity : 0 ≤ 1/(4*q)) (hp0 x).le
        simpa only [sq] using hh
      _ = _ := by field_simp; norm_num
  have hpoint (x y) : |D x y| ≤ 36*q/width := by
    have hM : 0 ≤ marked x y / (p x*p y) := div_nonneg (hm0 x y) (hpp x y).le
    have hI : 0 ≤ inactive x y / (p x*p y) := div_nonneg (hmean.1 x y) (hpp x y).le
    have hd : D x y = marked x y / (p x*p y) - inactive x y / (p x*p y) := by
      dsimp only [D, activeEndpointDensity, activeEndpointDifference, marked, inactive, p]
      exact sub_div _ _ _
    rw [hd]
    have hx := hmarked x y
    have hy := hinactive x y
    have hsum : 4*q/width + 32*q/width = 36*q/width := by ring
    rw [← hsum]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hM, abs_of_nonneg hI]; linarith)
  have hL1 : (∑ x, ∑ y, |marked x y-inactive x y|) ≤ 2 := by
    calc
      _ ≤ ∑ x, ∑ y, (marked x y+inactive x y) := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hm0 x y), abs_of_nonneg (hmean.1 x y)])
      _ = _ := by simp only [Finset.sum_add_distrib, hmass, hImass]; norm_num
  refine ⟨?_, hpoint, ?_, ?_, ?_⟩
  · change (∑ first, ∑ second, (marked first second - inactive first second)) = 0
    simp only [Finset.sum_sub_distrib, hmass, hImass, sub_self]
  · calc
      _ ≤ ∑ x, ∑ y, (36*q/width) * |marked x y-inactive x y| := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        have hh := mul_le_mul_of_nonneg_right (hpoint x y) (abs_nonneg (marked x y-inactive x y))
        convert hh using 1
        dsimp only [D, activeEndpointDensity, activeEndpointDifference]
        change p x*p y * ((marked x y-inactive x y)/(p x*p y))^2 = _
        rw [abs_div, abs_of_pos (mul_pos (hp0 x) (hp0 y))]
        field_simp
        rw [← sq, sq_abs]
      _ = (36*q/width) * (∑ x, ∑ y, |marked x y-inactive x y|) := by simp only [Finset.mul_sum]
      _ ≤ (36*q/width)*2 := mul_le_mul_of_nonneg_left hL1 (by positivity)
      _ = _ := by dsimp only [q,width]; ring
  · intro x
    calc
      _ ≤ ∑ y, p y * (36*q/width)^2 := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hpoint x y) 2) (hp0 y).le
      _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]
  · intro y
    calc
      _ ≤ ∑ x, p x * (36*q/width)^2 := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hpoint x y) 2) (hp0 x).le
      _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]

end
end AFT.V7Calibration

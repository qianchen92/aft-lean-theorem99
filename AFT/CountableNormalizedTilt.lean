import AFT.ClippedConvolution

/-! # Normalization of a uniform multiplicative error on an actual countable probability law -/
namespace AFT
open scoped BigOperators

/-- Normalizing a positive approximate density costs at most
`error / (1-error)` in total variation. Both masses are genuine normalized
countable laws; no unknown normalizer is treated as one. -/
theorem normalized_tilt_total_variation {State : Type*}
    (reference actual : State → ℝ)
    (href : ∀ state, 0 ≤ reference state)
    (hreference : Summable reference) (hactual : Summable actual)
    (href_one : ∑' state, reference state = 1)
    (hactual_one : ∑' state, actual state = 1)
    (scale error : ℝ) (herror : 0 ≤ error) (herror_one : error < 1)
    (hpoint : ∀ state, |actual state - scale * reference state| ≤
      error * scale * reference state) :
    (∑' state, |actual state-reference state|) / 2 ≤ error / (1-error) := by
  have hdiff := hactual.sub (hreference.mul_left scale)
  have hnorm : |1-scale| ≤ error*scale := by
    have ht := norm_tsum_le_tsum_norm hdiff.norm
    rw [hactual.tsum_sub (hreference.mul_left scale),tsum_mul_left,hactual_one,href_one,mul_one,Real.norm_eq_abs] at ht
    have hb := hdiff.norm.tsum_le_tsum (fun state => by
      simpa only [Real.norm_eq_abs] using hpoint state) (hreference.mul_left (error*scale))
    rw [tsum_mul_left,href_one,mul_one] at hb
    exact ht.trans hb
  have hs : scale ≤ 1/(1-error) := by
    apply (le_div_iff₀ (by linarith : 0<1-error)).mpr
    have hh' := (neg_le_abs (1-scale)).trans hnorm
    nlinarith
  have hbound (state : State) : |actual state-reference state| ≤
      (2*error*scale)*reference state := by
    calc
      _ = |(actual state-scale*reference state)+(scale-1)*reference state| := by congr 1; ring
      _ ≤ |actual state-scale*reference state|+|(scale-1)*reference state| := abs_add_le _ _
      _ ≤ error*scale*reference state+(error*scale)*reference state := by
        apply add_le_add (hpoint state)
        rw [abs_mul,abs_of_nonneg (href state),abs_sub_comm]
        exact mul_le_mul_of_nonneg_right hnorm (href state)
      _ = _ := by ring
  have hsum := (hactual.sub hreference).norm.tsum_le_tsum
    (fun state => by simpa only [Real.norm_eq_abs] using hbound state)
    (hreference.mul_left (2*error*scale))
  simp only [Real.norm_eq_abs,tsum_mul_left,href_one,mul_one] at hsum
  have hmul := mul_le_mul_of_nonneg_left hs herror
  rw [mul_one_div] at hmul
  linarith

end AFT

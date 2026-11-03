import AFT.SafeFiniteNeumann

/-! # Squared Hilbert error of averaging genuine finite translations -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Jensen's inequality is applied to the actual finite smoothing kernel,
retaining all displacement events. -/
theorem convolution_difference_square_le (source : FiniteDist G) (profile : G → ℝ) :
    (∑ color, (convolution source.weight profile color - profile color) ^ 2) ≤
      ∑ shift, source.weight shift * ∑ color, (profile (color - shift) - profile color) ^ 2 := by
  have heq (color : G) : convolution source.weight profile color - profile color =
      ∑ shift, source.weight shift * (profile (color - shift) - profile color) := by
    simp only [convolution_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, source.sum_one, one_mul]
  have hpoint (color : G) : (convolution source.weight profile color - profile color) ^ 2 ≤
      ∑ shift, source.weight shift * (profile (color - shift) - profile color) ^ 2 := by
    rw [heq]
    have hh : (∑ shift, source.weight shift * (profile (color - shift) - profile color)) ^ 2 ≤
        (∑ shift, source.weight shift) *
          ∑ shift, source.weight shift * (profile (color - shift) - profile color) ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      · intro shift _; exact source.nonneg _
      · intro shift _; exact mul_nonneg (source.nonneg _) (sq_nonneg _)
      · intro shift _; ring
    simpa only [source.sum_one, one_mul] using hh
  calc
    _ ≤ ∑ color, ∑ shift, source.weight shift * (profile (color - shift) - profile color) ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

theorem convolution_difference_square_le_uniform (source : FiniteDist G) (profile : G → ℝ) (bound : ℝ)
    (hbound : ∀ shift, source.weight shift ≠ 0 →
      (∑ color, (profile (color - shift) - profile color) ^ 2) ≤ bound) :
    (∑ color, (convolution source.weight profile color - profile color) ^ 2) ≤ bound := by
  calc
    _ ≤ ∑ shift, source.weight shift * ∑ color, (profile (color - shift) - profile color) ^ 2 :=
      convolution_difference_square_le source profile
    _ ≤ ∑ shift, source.weight shift * bound := by
      apply Finset.sum_le_sum
      intro shift _
      by_cases hs : source.weight shift = 0
      · simp only [hs, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hbound shift hs) (source.nonneg shift)
    _ = _ := by rw [← Finset.sum_mul, source.sum_one, one_mul]

omit [AddCommGroup G] in
/-- Full finite mixtures of joint profiles obey the same squared bound;
no rank-one decomposition of their output coordinates is used. -/
theorem probability_profile_mixture_square_le {σ : Type*} [Fintype σ]
    (source : FiniteDist σ) (profiles : σ → G → ℝ) :
    (∑ color, (∑ sample, source.weight sample * profiles sample color) ^ 2) ≤
      ∑ sample, source.weight sample * ∑ color, profiles sample color ^ 2 := by
  have hpoint (color : G) : (∑ sample, source.weight sample * profiles sample color) ^ 2 ≤
      ∑ sample, source.weight sample * profiles sample color ^ 2 := by
    have hh : (∑ sample, source.weight sample * profiles sample color) ^ 2 ≤
        (∑ sample, source.weight sample) * ∑ sample, source.weight sample * profiles sample color ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      · intro sample _; exact source.nonneg _
      · intro sample _; exact mul_nonneg (source.nonneg _) (sq_nonneg _)
      · intro sample _; ring
    simpa only [source.sum_one, one_mul] using hh
  calc
    _ ≤ ∑ color, ∑ sample, source.weight sample * profiles sample color ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

omit [AddCommGroup G] in
theorem probability_profile_mixture_square_le_uniform {σ : Type*} [Fintype σ]
    (source : FiniteDist σ) (profiles : σ → G → ℝ) (bound : ℝ)
    (hbound : ∀ sample, (∑ color, profiles sample color ^ 2) ≤ bound) :
    (∑ color, (∑ sample, source.weight sample * profiles sample color) ^ 2) ≤ bound := by
  exact (probability_profile_mixture_square_le source profiles).trans (by
    calc
      _ ≤ ∑ sample, source.weight sample * bound :=
        Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (hbound sample) (source.nonneg sample)
      _ = _ := by rw [← Finset.sum_mul, source.sum_one, one_mul])

theorem convolution_mixture_apply {σ : Type*} [Fintype σ] (kernel : G → ℝ)
    (weights : σ → ℝ) (profiles : σ → G → ℝ) (color : G) :
    convolution kernel (fun point => ∑ sample, weights sample * profiles sample point) color =
      ∑ sample, weights sample * convolution kernel (profiles sample) color := by
  simp only [convolution_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  apply Finset.sum_congr rfl
  intro shift _
  ring

/-- Repeated actual probability smoothing costs only the fixed number of
steps times the proved one-step error. -/
theorem probability_power_error_L2_le (source : FiniteDist G) (profile : G → ℝ) (order : ℕ) :
    countingL2 ((convolution source.weight ^ order) profile - profile) ≤
      order * countingL2 (convolution source.weight profile - profile) := by
  induction order with
  | zero => simp [countingL2]
  | succ order ih =>
    rw [pow_succ', Module.End.mul_apply]
    have heq : convolution source.weight ((convolution source.weight ^ order) profile) - profile =
        convolution source.weight ((convolution source.weight ^ order) profile - profile) +
          (convolution source.weight profile - profile) := by
      rw [map_sub]
      abel
    rw [heq]
    exact (countingL2_add _ _).trans ((add_le_add
      ((probability_convolution_L2_le source _).trans ih) le_rfl).trans_eq (by push_cast; ring))

end AFT.SafeConvolution

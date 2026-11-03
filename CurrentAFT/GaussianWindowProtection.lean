import AFT.CountableConditioning
import AFT.CountableProductVariation
import AFT.CountableFiniteChannel

/-! # Actual infinite Gaussian to actual protected-window comparison

The protected real mass is identified with the finite `windowGaussian`
law. Its full countable total variation is controlled by the actual deleted
Gaussian probability, before any source-independent public channel is used.
-/
namespace CurrentAFT.GaussianWindowProtection
open AFT GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def protectedMass (width : ℝ) (cutoff : ℕ) (point : ℤ) : ℝ :=
  restrictWindow (integerMass width) cutoff point / retainedFraction width cutoff

theorem integerMass_actual (width : ℝ) (hwidth : 0 < width) (point : ℤ) :
    integerMass width point = (integerGaussian width hwidth point).toReal :=
  (integerGaussian_toReal width hwidth point).symm

theorem protectedMass_nonneg (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) (point : ℤ) :
    0 ≤ protectedMass width cutoff point :=
  div_nonneg (restrictWindow_nonneg _ (integerMass_nonneg width hwidth) cutoff point)
    (retainedFraction_pos width cutoff hwidth).le

theorem protectedMass_summable (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) :
    Summable (protectedMass width cutoff) :=
  (Summable.of_nonneg_of_le (restrictWindow_nonneg _ (integerMass_nonneg width hwidth) cutoff)
    (restrictWindow_le _ (integerMass_nonneg width hwidth) cutoff) (summable_integerMass width hwidth)).div_const _

theorem protectedMass_sum (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) :
    (∑' point, protectedMass width cutoff point) = 1 := by
  unfold protectedMass
  rw [tsum_div_const, restrictWindow_sum,
    div_self (retainedFraction_pos width cutoff hwidth).ne']

/-- Exact finite-window realization of the normalized retained mass. -/
theorem protectedMass_window (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) (point : ℤ) :
    protectedMass width cutoff point =
      if hpoint : point ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) then
        (windowGaussian width cutoff).weight ⟨point, hpoint⟩ else 0 := by
  by_cases hpoint : point ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)
  · rw [dif_pos hpoint]
    change (if point ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) then integerMass width point else 0) /
      retainedFraction width cutoff = _
    rw [if_pos hpoint]
    change (weight width point / realNormalizer width) /
      (windowNormalizer width cutoff / realNormalizer width) = weight width point / windowNormalizer width cutoff
    field_simp [(zero_lt_one.trans_le (realNormalizer_ge_one width hwidth)).ne',
      (zero_lt_one.trans_le (windowNormalizer_ge_one width cutoff)).ne']
  · simp only [protectedMass, restrictWindow, if_neg hpoint, dif_neg hpoint, zero_div]

theorem protectedMass_zero (width : ℝ) (cutoff : ℕ) (point : ℤ)
    (hpoint : point ∉ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)) :
    protectedMass width cutoff point = 0 := by simp only [protectedMass, restrictWindow, if_neg hpoint, zero_div]

private theorem outside_window_iff (cutoff : ℕ) (point : ℤ) :
    ((cutoff + 1 : ℕ) : ℝ) ≤ |(point : ℝ)| ↔
      point ∉ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) := by
  have hcast : ((cutoff + 1 : ℕ) : ℝ) ≤ |(point : ℝ)| ↔ (cutoff : ℤ) + 1 ≤ |point| := by
    rw [← Int.cast_abs]
    norm_cast
  rw [hcast, Finset.mem_Icc, ← abs_le]
  omega

theorem removed_probability (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) :
    1 - retainedFraction width cutoff = clippingProbability width (cutoff + 1 : ℕ) hwidth := by
  rw [← removedWindow_mass width cutoff hwidth]
  unfold clippingProbability
  apply tsum_congr
  intro point
  rw [← integerMass_actual width hwidth point]
  by_cases hpoint : point ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)
  · rw [if_neg (fun hout => (outside_window_iff cutoff point).mp hout hpoint)]
    simp only [restrictWindow, if_pos hpoint, sub_self]
  · rw [if_pos ((outside_window_iff cutoff point).mpr hpoint)]
    simp only [restrictWindow, if_neg hpoint, sub_zero]

/-- One clipping cost for the entire scalar source, with its genuine
infinite Gaussian normalizer and genuine finite protected normalizer. -/
theorem scalar_tv (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) :
    (∑' point, |integerMass width point - protectedMass width cutoff point|) / 2 ≤
      clippingProbability width (cutoff + 1 : ℕ) hwidth := by
  have hretained : 0 < ∑' point, restrictWindow (integerMass width) cutoff point := by
    rw [restrictWindow_sum]
    exact retainedFraction_pos width cutoff hwidth
  have hh := normalized_deleted_total_variation (integerMass width) (restrictWindow (integerMass width) cutoff)
    (integerMass_nonneg width hwidth) (restrictWindow_nonneg _ (integerMass_nonneg width hwidth) cutoff)
    (restrictWindow_le _ (integerMass_nonneg width hwidth) cutoff) (summable_integerMass width hwidth) hretained
  rw [restrictWindow_sum, integerMass_sum width hwidth] at hh
  simp only [div_one] at hh
  rw [← removed_probability width cutoff hwidth]
  convert hh using 1
  congr 1
  apply tsum_congr
  intro point
  exact abs_sub_comm _ _

theorem protectedMix_eq_window {Output : Type*} [Fintype Output]
    (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) (channel : ℤ → FiniteDist Output) :
    FiniteDist.countableMix (protectedMass width cutoff) (protectedMass_nonneg width cutoff hwidth)
      (protectedMass_summable width cutoff hwidth) (protectedMass_sum width cutoff hwidth) channel =
        (windowGaussian width cutoff).mix (fun point => channel point.val) := by
  apply FiniteDist.ext
  intro output
  change (∑' point, protectedMass width cutoff point * (channel point).weight output) = _
  rw [tsum_eq_sum (s := Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ))
    (fun point hpoint => by rw [protectedMass_zero width cutoff point hpoint, zero_mul]), ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro point _
  rw [protectedMass_window width cutoff hwidth point.val, dif_pos point.property]

/-- The same arbitrary public channel is used for both source laws. -/
theorem scalar_channel_tv {Output : Type*} [Fintype Output]
    (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) (channel : ℤ → FiniteDist Output) :
    FiniteDist.TVBound
      (FiniteDist.countableMix (integerMass width) (integerMass_nonneg width hwidth)
        (summable_integerMass width hwidth) (integerMass_sum width hwidth) channel)
      ((windowGaussian width cutoff).mix (fun point => channel point.val))
      (clippingProbability width (cutoff + 1 : ℕ) hwidth) := by
  rw [← protectedMix_eq_window width cutoff hwidth channel]
  exact FiniteDist.countableMix_tvBound _ _ (integerMass_nonneg width hwidth)
    (protectedMass_nonneg width cutoff hwidth) (summable_integerMass width hwidth)
    (protectedMass_summable width cutoff hwidth) (integerMass_sum width hwidth)
    (protectedMass_sum width cutoff hwidth) channel _ (scalar_tv width cutoff hwidth)

end
end CurrentAFT.GaussianWindowProtection

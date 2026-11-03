import AFT.RootSlice
import AFT.Negligible

/-!
# The protected scalar sources and their zero atoms

The finite alphabet is an actual symmetric integer window. Its law is the
restriction and normalization of the same Gaussian weights as the infinite
source. In particular its zero atom is bounded using Poisson duality.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable section

abbrev Window (cutoff : ℕ) := ↥(Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ))

def windowZero (cutoff : ℕ) : Window cutoff :=
  ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

def windowNormalizer (width : ℝ) (cutoff : ℕ) : ℝ :=
  ∑ z : Window cutoff, weight width z

theorem windowNormalizer_ge_one (width : ℝ) (cutoff : ℕ) :
    1 ≤ windowNormalizer width cutoff := by
  have h := Finset.single_le_sum (f := fun z : Window cutoff => weight width z)
    (fun z _ => (weight_pos width z).le) (Finset.mem_univ (windowZero cutoff))
  simpa [windowZero, weight, windowNormalizer] using h

theorem windowNormalizer_le_real (width : ℝ) (cutoff : ℕ) (hw : 0 < width) :
    windowNormalizer width cutoff ≤ realNormalizer width := by
  unfold windowNormalizer realNormalizer
  rw [Finset.sum_coe_sort]
  exact (summable_weight width hw).sum_le_tsum _ (fun z _ => (weight_pos width z).le)

/-- Clipping at `|z| ≤ cutoff`; the manuscript's strict cutoff `B` is
obtained by taking `cutoff = B - 1`. -/
def windowGaussian (width : ℝ) (cutoff : ℕ) : FiniteDist (Window cutoff) :=
  FiniteDist.normalize (fun z => weight width z) (fun z => (weight_pos width z).le)
    (lt_of_lt_of_le zero_lt_one (windowNormalizer_ge_one width cutoff))

theorem windowGaussian_positive (width : ℝ) (cutoff : ℕ) (z : Window cutoff) :
    0 < (windowGaussian width cutoff).weight z :=
  div_pos (weight_pos width z)
    (lt_of_lt_of_le zero_lt_one (windowNormalizer_ge_one width cutoff))

theorem windowGaussian_zero (width : ℝ) (cutoff : ℕ) :
    (windowGaussian width cutoff).weight (windowZero cutoff) =
      1 / windowNormalizer width cutoff := by
  simp [windowGaussian, FiniteDist.normalize, windowZero, weight, windowNormalizer]

/-- The actual clipped zero atom has the required inverse-linear lower
bound, uniformly in the clipping window. -/
theorem windowGaussian_zero_lower (width : ℝ) (cutoff : ℕ) (hw : 1 ≤ width) :
    1 / ((1 + 2 / Real.pi) * width) ≤
      (windowGaussian width cutoff).weight (windowZero cutoff) := by
  rw [windowGaussian_zero]
  apply one_div_le_one_div_of_le
  · exact lt_of_lt_of_le zero_lt_one (windowNormalizer_ge_one width cutoff)
  · exact (windowNormalizer_le_real width cutoff (lt_of_lt_of_le zero_lt_one hw)).trans
      (realNormalizer_le_linear width hw)

/-- This is the actual independent two-source zero event used by the
marked chart activation. -/
theorem window_pair_zero (firstWidth secondWidth : ℝ) (cutoff : ℕ) :
    ((windowGaussian firstWidth cutoff).prod (windowGaussian secondWidth cutoff)).weight
      (windowZero cutoff, windowZero cutoff) =
      1 / (windowNormalizer firstWidth cutoff * windowNormalizer secondWidth cutoff) := by
  change (windowGaussian firstWidth cutoff).weight _ *
    (windowGaussian secondWidth cutoff).weight _ = _
  rw [windowGaussian_zero, windowGaussian_zero]
  ring

/-- The exact activation probability with `100 * featureCount` as the
reciprocal mark weight, including the two actual independent source atoms. -/
def activation (firstWidth secondWidth : ℝ) (cutoff featureCount : ℕ) : ℝ :=
  1 / (100 * (featureCount : ℝ)) *
    ((windowGaussian firstWidth cutoff).prod (windowGaussian secondWidth cutoff)).weight
      (windowZero cutoff, windowZero cutoff)

theorem activation_positive (firstWidth secondWidth : ℝ) (cutoff featureCount : ℕ)
    (hfeatures : 0 < featureCount) : 0 < activation firstWidth secondWidth cutoff featureCount := by
  unfold activation
  change 0 < 1 / (100 * (featureCount : ℝ)) *
    ((windowGaussian firstWidth cutoff).weight _ * (windowGaussian secondWidth cutoff).weight _)
  exact mul_pos (by positivity) (mul_pos (windowGaussian_positive _ _ _) (windowGaussian_positive _ _ _))

theorem activation_lower (firstWidth secondWidth : ℝ) (cutoff featureCount : ℕ)
    (hfirst : 1 ≤ firstWidth) (hsecond : 1 ≤ secondWidth) (hfeatures : 0 < featureCount) :
    1 / (100 * (featureCount : ℝ) * (1 + 2 / Real.pi) ^ 2 * firstWidth * secondWidth) ≤
      activation firstWidth secondWidth cutoff featureCount := by
  have h1 := windowGaussian_zero_lower firstWidth cutoff hfirst
  have h2 := windowGaussian_zero_lower secondWidth cutoff hsecond
  have hprod := mul_le_mul h1 h2 (by positivity) (windowGaussian_positive _ _ _).le
  have hscaled := mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ 1 / (100 * (featureCount : ℝ)))
  convert hscaled using 1
  · field_simp

/-- The protected root event is nonnull for every population, with the
correct integer zero-sum condition. -/
theorem window_root_probability_positive (width : ℝ) (cutoff population : ℕ) :
    0 < RootSlice.probability (fun _ : Fin population => windowGaussian width cutoff)
      (fun z => (z : ℤ)) 0 :=
  RootSlice.probability_positive _ _ (windowZero cutoff) rfl
    (fun _ => windowGaussian_positive width cutoff (windowZero cutoff))

end

end AFT.GaussianSource

import AFT.ClippedSource

/-!
# Uniform moments of the actual protected scalar law

The denominator is bounded below by actual lattice points inside one width.
An exponential-square tilt is exactly a wider Gaussian on the same window.
Neither estimate assumes a continuous Gaussian replacement.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

theorem windowNormalizer_lower_linear (width : ℝ) (cutoff : ℕ) (hw : 0 < width)
    (hcutoff : ⌊width⌋₊ ≤ cutoff) :
    Real.exp (-Real.pi) * width ≤ windowNormalizer width cutoff := by
  have hsubset : Finset.Icc (0 : ℤ) (⌊width⌋₊ : ℤ) ⊆
      Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := Finset.mem_Icc.mp hz
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hpoint (z : ℤ) (hz : z ∈ Finset.Icc (0 : ℤ) (⌊width⌋₊ : ℤ)) :
      Real.exp (-Real.pi) ≤ weight width z := by
    obtain ⟨hz0, hz1⟩ := Finset.mem_Icc.mp hz
    have hz0' : (0 : ℝ) ≤ z := by exact_mod_cast hz0
    have hz1' : (z : ℝ) ≤ (⌊width⌋₊ : ℝ) := by exact_mod_cast hz1
    have hzw : (z : ℝ) ≤ width := hz1'.trans (Nat.floor_le hw.le)
    have hsq : (z : ℝ) ^ 2 ≤ width ^ 2 := by nlinarith
    unfold weight
    apply Real.exp_le_exp.mpr
    have hc : 0 ≤ Real.pi / width ^ 2 := by positivity
    have hh := mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hc)
    have heq : -(Real.pi / width ^ 2) * width ^ 2 = -Real.pi := by field_simp
    simpa only [heq] using hh
  have hcard : ((Finset.Icc (0 : ℤ) (⌊width⌋₊ : ℤ)).card : ℝ) = (⌊width⌋₊ : ℝ) + 1 := by
    simp [Int.card_Icc]
  calc
    _ ≤ Real.exp (-Real.pi) * ((⌊width⌋₊ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one width).le (Real.exp_pos _).le
    _ = ∑ z ∈ Finset.Icc (0 : ℤ) (⌊width⌋₊ : ℤ), Real.exp (-Real.pi) := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      ring
    _ ≤ ∑ z ∈ Finset.Icc (0 : ℤ) (⌊width⌋₊ : ℤ), weight width z :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ z ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ), weight width z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun z _ _ => (weight_pos width z).le)
    _ = _ := by unfold windowNormalizer; rw [Finset.sum_coe_sort]

/-- Upper bound matching the inverse-width zero atom lower bound. -/
theorem windowGaussian_zero_upper (width : ℝ) (cutoff : ℕ) (hw : 0 < width)
    (hcutoff : ⌊width⌋₊ ≤ cutoff) :
    (windowGaussian width cutoff).weight (windowZero cutoff) ≤ Real.exp Real.pi / width := by
  rw [windowGaussian_zero]
  calc
    _ ≤ 1 / (Real.exp (-Real.pi) * width) :=
      one_div_le_one_div_of_le (by positivity) (windowNormalizer_lower_linear width cutoff hw hcutoff)
    _ = _ := by rw [Real.exp_neg]; field_simp

/-- The exponential-square tilt is a wider integer Gaussian on precisely
the same clipping window. -/
theorem windowGaussian_exp_square (width : ℝ) (cutoff : ℕ) (hw : 0 < width) :
    (windowGaussian width cutoff).expectation
      (fun z => Real.exp (Real.pi / 2 * ((z : ℝ) / width) ^ 2)) =
      windowNormalizer (Real.sqrt 2 * width) cutoff / windowNormalizer width cutoff := by
  have hwidth : (Real.sqrt 2 * width) ^ 2 = 2 * width ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold FiniteDist.expectation windowGaussian FiniteDist.normalize
  change (∑ z : Window cutoff, weight width z / windowNormalizer width cutoff *
    Real.exp (Real.pi / 2 * ((z : ℝ) / width) ^ 2)) = _
  unfold windowNormalizer
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  rw [div_mul_eq_mul_div]
  congr 1
  unfold weight
  rw [← Real.exp_add, hwidth]
  congr 1
  field_simp
  ring

/-- A numerical exponential-square moment bound uniform in width and
cutoff, once the clipping window contains one standard width. -/
theorem windowGaussian_exp_square_bound (width : ℝ) (cutoff : ℕ) (hw : 1 ≤ width)
    (hcutoff : ⌊width⌋₊ ≤ cutoff) :
    (windowGaussian width cutoff).expectation
      (fun z => Real.exp (Real.pi / 2 * ((z : ℝ) / width) ^ 2)) ≤
        (1 + 2 / Real.pi) * Real.sqrt 2 * Real.exp Real.pi := by
  have hw0 : 0 < width := lt_of_lt_of_le zero_lt_one hw
  have hs : 1 ≤ Real.sqrt 2 := by norm_num
  have hwider : 1 ≤ Real.sqrt 2 * width := by nlinarith [Real.sqrt_nonneg 2]
  rw [windowGaussian_exp_square width cutoff hw0]
  have hn := (windowNormalizer_le_real (Real.sqrt 2 * width) cutoff (by positivity)).trans
    (realNormalizer_le_linear (Real.sqrt 2 * width) hwider)
  calc
    _ ≤ ((1 + 2 / Real.pi) * (Real.sqrt 2 * width)) /
        (Real.exp (-Real.pi) * width) := div_le_div₀
      (by positivity) hn (by positivity) (windowNormalizer_lower_linear width cutoff hw0 hcutoff)
    _ = _ := by rw [Real.exp_neg]; field_simp

end AFT.GaussianSource

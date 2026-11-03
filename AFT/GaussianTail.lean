import AFT.GaussianSource
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# A quantitative clipping bound for the actual integer Gaussian

All masses are summed on the infinite integer lattice. Polynomial bounds on
the normalizer are proved by a geometric comparison; no Gaussian tail or
normalizing-constant estimate is assumed.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable def realNormalizer (width : ℝ) : ℝ := ∑' z : ℤ, weight width z

theorem realNormalizer_ge_one (width : ℝ) (hw : 0 < width) :
    1 ≤ realNormalizer width := by
  have h := (summable_weight width hw).le_tsum (0 : ℤ) (fun z _ => (weight_pos width z).le)
  simpa [weight, realNormalizer] using h

theorem realNormalizer_eq_toReal (width : ℝ) :
    realNormalizer width = (normalizer width).toReal := by
  rw [normalizer, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp [realNormalizer, ENNReal.toReal_ofReal, (weight_pos width _).le]

theorem integerGaussian_toReal (width : ℝ) (hw : 0 < width) (z : ℤ) :
    (integerGaussian width hw z).toReal = weight width z / realNormalizer width := by
  rw [integerGaussian, PMF.normalize_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (weight_pos width z).le]
  change weight width z * (normalizer width).toReal⁻¹ = _
  rw [← realNormalizer_eq_toReal]
  rfl

theorem weight_even (width : ℝ) : Function.Even (weight width) := by
  intro z
  simp [weight]

/-- The nonzero lattice points are bounded by a genuine geometric series. -/
theorem realNormalizer_le_geometric (width : ℝ) (hw : 0 < width) :
    realNormalizer width ≤
      1 + 2 * (Real.exp (-(Real.pi / width ^ 2)) /
        (1 - Real.exp (-(Real.pi / width ^ 2)))) := by
  let coefficient := Real.pi / width ^ 2
  have hc : 0 < coefficient := div_pos Real.pi_pos (sq_pos_of_pos hw)
  have hr0 : 0 ≤ Real.exp (-coefficient) := (Real.exp_pos _).le
  have hr1 : Real.exp (-coefficient) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
  have hgeom : Summable (fun n : ℕ => Real.exp (-coefficient) ^ n) :=
    summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])
  have hgeom' : Summable (fun n : ℕ => Real.exp (-coefficient) ^ (n + 1)) := by
    simpa only [pow_succ] using hgeom.mul_right (Real.exp (-coefficient))
  have hnat : Summable (fun n : ℕ => weight width ((n + 1 : ℕ) : ℤ)) :=
    (summable_weight width hw).comp_injective
      (fun a b h => Nat.succ.inj (Int.ofNat_inj.mp h))
  have hpoint (n : ℕ) : weight width ((n + 1 : ℕ) : ℤ) ≤
      Real.exp (-coefficient) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    unfold weight
    push_cast
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change -coefficient * ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) * -coefficient
    nlinarith [mul_nonneg hc.le (mul_nonneg hn (by linarith : 0 ≤ (n : ℝ) + 1))]
  have hsum := hnat.tsum_le_tsum hpoint hgeom'
  have heq : (∑' n : ℕ, Real.exp (-coefficient) ^ (n + 1)) =
      Real.exp (-coefficient) / (1 - Real.exp (-coefficient)) := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])]
    ring
  rw [heq] at hsum
  unfold realNormalizer
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (weight_even width) (summable_weight width hw)]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => weight width (n : ℤ))]
  simp only [weight, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    Real.exp_zero, nsmul_eq_mul]
  simpa only [weight, coefficient] using add_le_add (le_refl (1 : ℝ))
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))

theorem exponential_geometric_le_inv (coefficient : ℝ) (hc : 0 < coefficient) :
    Real.exp (-coefficient) / (1 - Real.exp (-coefficient)) ≤ coefficient⁻¹ := by
  have he : 1 < Real.exp coefficient := Real.one_lt_exp_iff.mpr hc
  have he0 : Real.exp coefficient ≠ 0 := (Real.exp_pos _).ne'
  have hd : Real.exp coefficient - 1 ≠ 0 := (sub_pos.mpr he).ne'
  have hident : Real.exp (-coefficient) / (1 - Real.exp (-coefficient)) =
      (Real.exp coefficient - 1)⁻¹ := by
    rw [Real.exp_neg]
    field_simp
  rw [hident]
  exact inv_anti₀ hc (by linarith [Real.add_one_le_exp coefficient])

/-- A deliberately coarse polynomial bound is enough for clipping errors. -/
theorem realNormalizer_le_quadratic (width : ℝ) (hw : 0 < width) :
    realNormalizer width ≤ 1 + 2 * width ^ 2 / Real.pi := by
  have hc : 0 < Real.pi / width ^ 2 := div_pos Real.pi_pos (sq_pos_of_pos hw)
  calc
    _ ≤ 1 + 2 * (Real.exp (-(Real.pi / width ^ 2)) /
        (1 - Real.exp (-(Real.pi / width ^ 2)))) := realNormalizer_le_geometric width hw
    _ ≤ 1 + 2 * (Real.pi / width ^ 2)⁻¹ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (exponential_geometric_le_inv _ hc)
        (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by rw [inv_div]; ring

/-- Exact Poisson duality of the lattice normalizing constant. -/
theorem realNormalizer_duality (width : ℝ) (hw : 0 < width) :
    realNormalizer width = width * realNormalizer (1 / width) := by
  have ht := Real.tsum_exp_neg_mul_int_sq (a := 1 / width ^ 2) (by positivity : 0 < 1 / width ^ 2)
  have hroot : (1 / width ^ 2) ^ (1 / 2 : ℝ) = 1 / width := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
      Real.sqrt_one, Real.sqrt_sq hw.le]
  rw [hroot, one_div_one_div] at ht
  convert ht using 1
  · unfold realNormalizer
    congr 1
    ext z
    unfold weight
    congr 1
    ring
  · congr 1
    unfold realNormalizer
    congr 1
    ext z
    unfold weight
    congr 1
    field_simp

/-- A linear normalizer bound follows from duality, without comparison to
an unproved Gaussian integral estimate. -/
theorem realNormalizer_le_linear (width : ℝ) (hw : 1 ≤ width) :
    realNormalizer width ≤ (1 + 2 / Real.pi) * width := by
  have hw0 : 0 < width := lt_of_lt_of_le zero_lt_one hw
  rw [realNormalizer_duality width hw0]
  have h := realNormalizer_le_quadratic (1 / width) (by positivity)
  have hi : 0 ≤ 1 / width := by positivity
  have hi1 : 1 / width ≤ 1 := (div_le_one hw0).mpr hw
  have hisq : (1 / width) ^ 2 ≤ 1 := by nlinarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsmall : 1 + 2 * (1 / width) ^ 2 / Real.pi ≤ 1 + 2 / Real.pi := by
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (by nlinarith) hpi.le
  calc
    _ ≤ width * (1 + 2 / Real.pi) := mul_le_mul_of_nonneg_left (h.trans hsmall) hw0.le
    _ = _ := mul_comm _ _

/-- Exact unnormalized mass removed by clipping at the stated absolute
cutoff. The event includes the boundary, as in the manuscript's strict
protected inequalities. -/
noncomputable def clippingMass (width cutoff : ℝ) : ℝ :=
  ∑' z : ℤ, if cutoff ≤ |(z : ℝ)| then weight width z else 0

theorem summable_clippingMass (width cutoff : ℝ) (hw : 0 < width) :
    Summable (fun z : ℤ => if cutoff ≤ |(z : ℝ)| then weight width z else 0) := by
  apply Summable.of_nonneg_of_le _ _ (summable_weight width hw)
  · intro z
    split_ifs
    · exact (weight_pos width z).le
    · rfl
  · intro z
    split_ifs
    · rfl
    · exact (weight_pos width z).le

/-- Splitting the Gaussian exponent in half provides a uniform tail bound
by the normalizer of a genuinely wider integer Gaussian. -/
theorem clippingMass_le (width cutoff : ℝ) (hw : 0 < width) (hc : 0 ≤ cutoff) :
    clippingMass width cutoff ≤
      Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        realNormalizer (Real.sqrt 2 * width) := by
  have hw2 : 0 < Real.sqrt 2 * width := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hw
  have hsq : (Real.sqrt 2 * width) ^ 2 = 2 * width ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpoint (z : ℤ) : (if cutoff ≤ |(z : ℝ)| then weight width z else 0) ≤
      Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        weight (Real.sqrt 2 * width) z := by
    split_ifs with hz
    · have hzsq : cutoff ^ 2 ≤ (z : ℝ) ^ 2 := by nlinarith [sq_abs (z : ℝ)]
      unfold weight
      rw [hsq, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcoef : 0 ≤ Real.pi / width ^ 2 := by positivity
      have hh : -Real.pi * cutoff ^ 2 / (2 * width ^ 2) +
          -(Real.pi / (2 * width ^ 2)) * (z : ℝ) ^ 2 =
          -(Real.pi / width ^ 2) * (cutoff ^ 2 + (z : ℝ) ^ 2) / 2 := by ring
      rw [hh]
      nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hzsq)]
    · exact mul_nonneg (Real.exp_pos _).le (weight_pos _ z).le
  have hsum := (summable_clippingMass width cutoff hw).tsum_le_tsum hpoint
    ((summable_weight _ hw2).mul_left (Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2))))
  have heq : (∑' z : ℤ, Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
      weight (Real.sqrt 2 * width) z) =
      Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        realNormalizer (Real.sqrt 2 * width) := tsum_mul_left
  exact hsum.trans_eq heq

/-- Actual normalized probability of violating the strict protected cutoff. -/
noncomputable def clippingProbability (width cutoff : ℝ) (hw : 0 < width) : ℝ :=
  ∑' z : ℤ, if cutoff ≤ |(z : ℝ)| then (integerGaussian width hw z).toReal else 0

theorem clippingProbability_eq (width cutoff : ℝ) (hw : 0 < width) :
    clippingProbability width cutoff hw = clippingMass width cutoff / realNormalizer width := by
  unfold clippingProbability clippingMass
  simp_rw [integerGaussian_toReal]
  have heq (z : ℤ) : (if cutoff ≤ |(z : ℝ)| then weight width z / realNormalizer width else 0) =
      (if cutoff ≤ |(z : ℝ)| then weight width z else 0) / realNormalizer width := by
    split_ifs <;> simp
  simp_rw [heq]
  exact tsum_div_const

/-- A completely explicit Gaussian clipping bound. The coarse quadratic
prefactor is harmless for every protected cutoff used in V7. -/
theorem clippingProbability_le (width cutoff : ℝ) (hw : 0 < width) (hc : 0 ≤ cutoff) :
    clippingProbability width cutoff hw ≤
      Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        (1 + 4 * width ^ 2 / Real.pi) := by
  have hm : 0 ≤ clippingMass width cutoff := tsum_nonneg (fun z => by
    split_ifs
    · exact (weight_pos width z).le
    · rfl)
  have hw2 : 0 < Real.sqrt 2 * width := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hw
  have hn := realNormalizer_le_quadratic (Real.sqrt 2 * width) hw2
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hn
  have hn' : realNormalizer (Real.sqrt 2 * width) ≤ 1 + 4 * width ^ 2 / Real.pi := by
    convert hn using 1
    ring
  calc
    _ = clippingMass width cutoff / realNormalizer width := clippingProbability_eq width cutoff hw
    _ ≤ clippingMass width cutoff := div_le_self hm (realNormalizer_ge_one width hw)
    _ ≤ Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        realNormalizer (Real.sqrt 2 * width) := clippingMass_le width cutoff hw hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hn' (Real.exp_pos _).le

end AFT.GaussianSource

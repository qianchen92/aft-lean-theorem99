import AFT.RootGaussianApprox
import AFT.Parameters

/-!
# Explicit polynomial-exponential bounds for the root convolution error
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

/-- A finite-degree estimate for accumulated multiplicative errors. -/
theorem one_add_power_sub_one_le (error : ℝ) (count : ℕ) (he : 0 ≤ error)
    (hsmall : (count : ℝ) * error ≤ 1) :
    (1 + error) ^ count - 1 ≤ Real.exp 1 * count * error := by
  have hpow : (1 + error) ^ count ≤ Real.exp 1 := by
    calc
      _ ≤ Real.exp error ^ count := pow_le_pow_left₀ (by linarith)
        (by linarith [Real.add_one_le_exp error]) count
      _ = Real.exp ((count : ℝ) * error) := (Real.exp_nat_mul error count).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsmall
  have hsum : (∑ i ∈ Finset.range count, (1 + error) ^ i) ≤ (count : ℝ) * Real.exp 1 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range count, Real.exp 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + error)
          (Finset.mem_range.mp hi).le).trans hpow
      _ = _ := by simp
  have hgeom := geom_sum_mul (1 + error) count
  have hbase : 1 + error - 1 = error := by ring
  rw [hbase] at hgeom
  rw [← hgeom]
  have h := mul_le_mul_of_nonneg_right hsum he
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

theorem normalizer_div_width_le (width error : ℝ) (hw : 0 < width)
    (he : thetaError (width / Real.sqrt 2) ≤ error) :
    realNormalizer width / width ≤ 1 + error := by
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hbase : 0 < width / Real.sqrt 2 := by positivity
  have hwidth : width / Real.sqrt 2 ≤ width := div_le_self hw.le hroot
  have ht := (theta_relative_error_exp width 0 hw).trans
    ((thetaError_antitone _ _ hbase hwidth).trans he)
  have heq : theta width 0 = realNormalizer width := by
    unfold theta realNormalizer shiftedWeight weight
    simp
  rw [heq] at ht
  have hu := (abs_le.mp ht).2
  linarith

/-- A polynomial lower bound for the comparison mass, whenever the center
lies within one standard Gaussian scale and the accumulated theta error is
small. This is the source of the relative clipping estimate. -/
theorem gaussianSumApprox_inv_le (width error : ℝ) (merges : ℕ) (target : ℤ)
    (hw : 0 < width) (he0 : 0 ≤ error)
    (he : thetaError (width / Real.sqrt 2) ≤ error)
    (hsmall : ((merges + 1 : ℕ) : ℝ) * error ≤ 1)
    (hcenter : Real.pi * (target : ℝ) ^ 2 ≤ powerWidth width merges ^ 2) :
    (gaussianSumApprox width merges target)⁻¹ ≤ Real.exp 2 * powerWidth width merges := by
  have hnormalizer : 0 < realNormalizer width := zero_lt_one.trans_le (realNormalizer_ge_one width hw)
  have hratio : (realNormalizer width / width) ^ (merges + 1) ≤ Real.exp 1 := by
    calc
      _ ≤ (1 + error) ^ (merges + 1) := pow_le_pow_left₀ (by positivity)
        (normalizer_div_width_le width error hw he) _
      _ ≤ Real.exp error ^ (merges + 1) := pow_le_pow_left₀ (by linarith)
        (by linarith [Real.add_one_le_exp error]) _
      _ = Real.exp (((merges + 1 : ℕ) : ℝ) * error) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsmall
  have hp := powerWidth_pos width hw merges
  have hquad : Real.pi * (target : ℝ) ^ 2 / powerWidth width merges ^ 2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hp)).mpr hcenter
  have hexp : Real.exp (Real.pi * (target : ℝ) ^ 2 / powerWidth width merges ^ 2) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hquad
  have heq : (gaussianSumApprox width merges target)⁻¹ =
      (realNormalizer width / width) ^ (merges + 1) * powerWidth width merges *
        Real.exp (Real.pi * (target : ℝ) ^ 2 / powerWidth width merges ^ 2) := by
    unfold gaussianSumApprox gaussianKernel weight
    rw [mul_inv_rev, inv_div, ← inv_pow, inv_div]
    have ht : -(Real.pi / powerWidth width merges ^ 2) * (target : ℝ) ^ 2 =
        -(Real.pi * (target : ℝ) ^ 2 / powerWidth width merges ^ 2) := by ring
    rw [ht, Real.exp_neg, div_eq_mul_inv, inv_inv]
    ring
  rw [heq]
  calc
    _ ≤ (Real.exp 1 * powerWidth width merges) * Real.exp 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hratio hp.le) hexp (Real.exp_pos _).le
        (mul_nonneg (Real.exp_pos _).le hp.le)
    _ = _ := by rw [mul_right_comm, ← Real.exp_add]; norm_num

/-- An explicit finite-parameter error estimate with polynomial prefactors. -/
theorem rootSumError_le (width error : ℝ) (cutoff merges : ℕ) (target : ℤ)
    (hw : 0 < width) (he0 : 0 ≤ error) (he1 : error ≤ 1)
    (he : thetaError (width / Real.sqrt 2) ≤ error)
    (hsmall : ((merges + 1 : ℕ) : ℝ) * error ≤ 1)
    (hcenter : Real.pi * (target : ℝ) ^ 2 ≤ powerWidth width merges ^ 2) :
    rootSumError width error cutoff merges target ≤
      (Real.exp 1 + 1) * merges * error +
        clippingError width cutoff (merges + 1) * (Real.exp 2 * powerWidth width merges) := by
  have hsmall' : (merges : ℝ) * error ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ merges :
      (merges : ℝ) ≤ ((merges + 1 : ℕ) : ℝ)) he0
    exact h.trans hsmall
  have h1 := one_add_power_sub_one_le error merges he0 hsmall'
  have h2 := one_sub_power_le (1 - error) (by linarith) (by linarith) merges
  have h3 := mul_le_mul_of_nonneg_left
    (gaussianSumApprox_inv_le width error merges target hw he0 he hsmall hcenter)
    (clippingError_nonneg width cutoff (merges + 1))
  unfold rootSumError
  rw [div_eq_mul_inv]
  nlinarith

noncomputable def v7RootWidth (parameter : ℕ) : ℝ := Real.sqrt 8 * parameter
noncomputable def v7RootThetaBound (parameter : ℕ) : ℝ :=
  4 * Real.exp (-4 * Real.pi * (parameter : ℝ) ^ 2)

noncomputable def v7RootErrorBound (parameter : ℕ) : ℝ :=
  8 * (Real.exp 1 + 1) * (parameter : ℝ) ^ 60 * Real.exp (-4 * Real.pi * (parameter : ℝ) ^ 2) +
    (8 * Real.exp 2 * (1 + 32 / Real.pi)) * (parameter : ℝ) ^ 93 *
      Real.exp (-(Real.pi / 4) * (parameter : ℝ) ^ 2)

theorem v7RootErrorBound_negligible : AFT.Negligible v7RootErrorBound := by
  have h1 := AFT.negligible_polynomial_stretched_exponential
    (8 * (Real.exp 1 + 1)) 60 2 (4 * Real.pi) (by positivity) (by norm_num) (by positivity)
  have h2 := AFT.negligible_polynomial_stretched_exponential
    (8 * Real.exp 2 * (1 + 32 / Real.pi)) 93 2 (Real.pi / 4) (by positivity) (by norm_num) (by positivity)
  have h := h1.add h2
  convert h using 1
  funext parameter
  unfold v7RootErrorBound
  simp only [Real.rpow_two, neg_mul, mul_assoc]

theorem v7RootWidth_sq (parameter : ℕ) : v7RootWidth parameter ^ 2 = 8 * (parameter : ℝ) ^ 2 := by
  rw [v7RootWidth, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]

theorem v7RootThetaBound_valid (parameter : ℕ) (hp : 1 ≤ parameter) :
    thetaError (v7RootWidth parameter / Real.sqrt 2) ≤ v7RootThetaBound parameter := by
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hsq : (v7RootWidth parameter / Real.sqrt 2) ^ 2 = 4 * (parameter : ℝ) ^ 2 := by
    rw [div_pow, v7RootWidth_sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hw0 : 0 ≤ v7RootWidth parameter / Real.sqrt 2 := by unfold v7RootWidth; positivity
  have hw1 : 1 ≤ v7RootWidth parameter / Real.sqrt 2 := by
    apply (sq_le_sq₀ zero_le_one hw0).mp
    rw [hsq]
    nlinarith
  have h := thetaError_le_four_exp _ hw1
  rw [hsq] at h
  convert h using 1
  unfold v7RootThetaBound
  congr 2
  ring

/-- Uniform pointwise root-error envelope at the manuscript's width. The
remaining conditions are explicit arithmetic smallness and center bounds. -/
theorem v7_rootSumError_envelope (parameter cutoff merges : ℕ) (target : ℤ)
    (hp : 1 ≤ parameter)
    (hcount : ((merges + 1 : ℕ) : ℝ) ≤ 2 * (parameter : ℝ) ^ 60)
    (hcut : 2 * (parameter : ℝ) ^ 2 ≤ cutoff)
    (hsmall : ((merges + 1 : ℕ) : ℝ) * v7RootThetaBound parameter ≤ 1)
    (hcenter : Real.pi * (target : ℝ) ^ 2 ≤ powerWidth (v7RootWidth parameter) merges ^ 2) :
    rootSumError (v7RootWidth parameter) (v7RootThetaBound parameter) cutoff merges target ≤
      v7RootErrorBound parameter := by
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < parameter := zero_lt_one.trans_le hp'
  have hw : 0 < v7RootWidth parameter := by unfold v7RootWidth; positivity
  have he0 : 0 ≤ v7RootThetaBound parameter := by unfold v7RootThetaBound; positivity
  have he1 : v7RootThetaBound parameter ≤ 1 := by
    have hm : (1 : ℝ) ≤ (merges + 1 : ℕ) := by exact_mod_cast Nat.succ_pos merges
    nlinarith
  have hbound := rootSumError_le (v7RootWidth parameter) (v7RootThetaBound parameter)
    cutoff merges target hw he0 he1 (v7RootThetaBound_valid parameter hp) hsmall hcenter
  have hwidth : powerWidth (v7RootWidth parameter) merges ≤ 4 * (parameter : ℝ) ^ 31 := by
    apply (sq_le_sq₀ (powerWidth_pos _ hw merges).le (by positivity)).mp
    rw [powerWidth_sq, v7RootWidth_sq]
    have hh := mul_le_mul_of_nonneg_right hcount (by positivity : 0 ≤ 8 * (parameter : ℝ) ^ 2)
    convert hh using 1
    ring
  have htail : Real.exp (-Real.pi * (cutoff : ℝ) ^ 2 / (2 * v7RootWidth parameter ^ 2)) ≤
      Real.exp (-(Real.pi / 4) * (parameter : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [v7RootWidth_sq]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (8 * (parameter : ℝ) ^ 2))).mpr
    have hc2 : (2 * (parameter : ℝ) ^ 2) ^ 2 ≤ (cutoff : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (Nat.cast_nonneg cutoff)).mpr hcut
    nlinarith [Real.pi_pos]
  have hp2 : 1 ≤ (parameter : ℝ) ^ 2 := by nlinarith
  have hpoly : 1 + 4 * v7RootWidth parameter ^ 2 / Real.pi ≤
      (1 + 32 / Real.pi) * (parameter : ℝ) ^ 2 := by
    rw [v7RootWidth_sq]
    calc
      _ = 1 + (32 / Real.pi) * (parameter : ℝ) ^ 2 := by ring
      _ ≤ _ := by nlinarith
  have hclip : clippingError (v7RootWidth parameter) cutoff (merges + 1) ≤
      2 * (1 + 32 / Real.pi) * (parameter : ℝ) ^ 62 *
        Real.exp (-(Real.pi / 4) * (parameter : ℝ) ^ 2) := by
    unfold clippingError
    calc
      _ ≤ (2 * (parameter : ℝ) ^ 60) *
          (Real.exp (-(Real.pi / 4) * (parameter : ℝ) ^ 2) *
            ((1 + 32 / Real.pi) * (parameter : ℝ) ^ 2)) := by
        gcongr
      _ = _ := by ring
  have hmerges : (merges : ℝ) ≤ 2 * (parameter : ℝ) ^ 60 := by
    have h : (merges : ℝ) ≤ ((merges + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ merges
    exact h.trans hcount
  apply hbound.trans
  unfold v7RootErrorBound v7RootThetaBound
  have hfirst := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmerges (by positivity : 0 ≤ Real.exp 1 + 1)) he0
  dsimp [v7RootThetaBound] at hfirst
  have hsecond := mul_le_mul hclip (mul_le_mul_of_nonneg_left hwidth (Real.exp_pos 2).le)
    (mul_nonneg (Real.exp_pos 2).le (powerWidth_pos _ hw merges).le)
    (by positivity : 0 ≤ 2 * (1 + 32 / Real.pi) * (parameter : ℝ) ^ 62 *
      Real.exp (-(Real.pi / 4) * (parameter : ℝ) ^ 2))
  have hh := add_le_add hfirst hsecond
  convert hh using 1
  ring

open Filter
open scoped Topology

/-- The concrete width and cutoff powers make the full root-sum relative
error negligible uniformly over a fixed number of clipped coordinates.
The count range is deliberately wider than the V7 body populations. -/
theorem v7_rootSumError_negligible (fixedOrder : ℕ)
    (count cutoff : ℕ → ℕ) (target : ℕ → ℤ)
    (hcountL : ∀ᶠ parameter : ℕ in atTop, parameter ^ 3 ≤ count parameter)
    (hcountU : ∀ᶠ parameter : ℕ in atTop, count parameter ≤ 2 * parameter ^ 60)
    (hcutoff : ∀ᶠ parameter : ℕ in atTop, 2 * parameter ^ 2 ≤ cutoff parameter)
    (htarget : ∀ᶠ parameter : ℕ in atTop,
      |(target parameter : ℝ)| ≤ 3 * fixedOrder * (parameter : ℝ) ^ 2) :
    AFT.Negligible (fun parameter => rootSumError (v7RootWidth parameter)
      (v7RootThetaBound parameter) (cutoff parameter) (count parameter - 1) (target parameter)) := by
  have hN := AFT.negligible_polynomial_stretched_exponential
    8 60 2 (4 * Real.pi) (by norm_num) (by norm_num) (by positivity)
  have hsmallPoly : ∀ᶠ parameter : ℕ in atTop,
      8 * (parameter : ℝ) ^ 60 * Real.exp (-4 * Real.pi * (parameter : ℝ) ^ 2) ≤ 1 := by
    filter_upwards [hN 0] with parameter h
    have h' := (le_abs_self _).trans h
    simpa only [pow_zero, div_one, Real.rpow_two, neg_mul] using h'
  have hlarge : ∀ᶠ parameter : ℕ in atTop, 9 * Real.pi * (fixedOrder : ℝ) ^ 2 ≤ 8 * parameter := by
    have ht : Tendsto (fun parameter : ℕ => (parameter : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_ge_atTop (9 * Real.pi * (fixedOrder : ℝ) ^ 2 / 8))]
      with parameter hp
    linarith
  apply v7RootErrorBound_negligible.of_eventually_le
  filter_upwards [hcountL, hcountU, hcutoff, htarget, hsmallPoly, hlarge, eventually_ge_atTop 1]
    with parameter hcL hcU hcut htarget hsmall hlarge hp
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < parameter := zero_lt_one.trans_le hp'
  have hcpos : 0 < count parameter := (pow_pos (by omega : 0 < parameter) 3).trans_le hcL
  have hcEq : count parameter - 1 + 1 = count parameter := Nat.sub_add_cancel hcpos
  have hcL' : (parameter : ℝ) ^ 3 ≤ count parameter := by exact_mod_cast hcL
  have hcU' : (count parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 60 := by exact_mod_cast hcU
  have hcut' : 2 * (parameter : ℝ) ^ 2 ≤ cutoff parameter := by exact_mod_cast hcut
  have hw : 0 < v7RootWidth parameter := by unfold v7RootWidth; positivity
  have he0 : 0 ≤ v7RootThetaBound parameter := by unfold v7RootThetaBound; positivity
  have hsmall' : (count parameter : ℝ) * v7RootThetaBound parameter ≤ 1 := by
    apply le_trans _ hsmall
    unfold v7RootThetaBound
    have hh := mul_le_mul_of_nonneg_right hcU'
      (by positivity : 0 ≤ 4 * Real.exp (-4 * Real.pi * (parameter : ℝ) ^ 2))
    convert hh using 1
    ring
  have he1 : v7RootThetaBound parameter ≤ 1 := by
    have hc1 : (1 : ℝ) ≤ count parameter := by exact_mod_cast hcpos
    nlinarith
  have hcenter : Real.pi * (target parameter : ℝ) ^ 2 ≤
      powerWidth (v7RootWidth parameter) (count parameter - 1) ^ 2 := by
    rw [powerWidth_sq, hcEq, v7RootWidth_sq]
    have hsq : (target parameter : ℝ) ^ 2 ≤ (3 * fixedOrder * (parameter : ℝ) ^ 2) ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (target parameter : ℝ)) (by positivity)).mpr htarget
      simpa only [sq_abs] using hh
    calc
      _ ≤ Real.pi * (3 * fixedOrder * (parameter : ℝ) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
      _ = (9 * Real.pi * (fixedOrder : ℝ) ^ 2) * (parameter : ℝ) ^ 4 := by ring
      _ ≤ (8 * parameter) * (parameter : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = (parameter : ℝ) ^ 3 * (8 * (parameter : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcL' (by positivity)
  have hbound := v7_rootSumError_envelope parameter (cutoff parameter) (count parameter - 1)
    (target parameter) hp (by simpa only [hcEq] using hcU') hcut'
    (by simpa only [hcEq] using hsmall') hcenter
  have herr0 : 0 ≤ rootSumError (v7RootWidth parameter) (v7RootThetaBound parameter)
      (cutoff parameter) (count parameter - 1) (target parameter) := by
    exact (abs_nonneg _).trans (window_root_gaussian_relative_error _ _ _ _ hw he0 he1
      (v7RootThetaBound_valid parameter hp) _)
  have hbound0 : 0 ≤ v7RootErrorBound parameter := by unfold v7RootErrorBound; positivity
  rw [abs_of_nonneg herr0, abs_of_nonneg hbound0]
  exact hbound

/-- The convolution error envelope is uniform over every protected center.
The threshold depends on the fixed order but not on the center. -/
theorem v7_rootSumError_uniform_envelope (fixedOrder : ℕ)
    (count cutoff : ℕ → ℕ)
    (hcountL : ∀ᶠ parameter : ℕ in atTop, parameter ^ 3 ≤ count parameter)
    (hcountU : ∀ᶠ parameter : ℕ in atTop, count parameter ≤ 2 * parameter ^ 60)
    (hcutoff : ∀ᶠ parameter : ℕ in atTop, 2 * parameter ^ 2 ≤ cutoff parameter) :
    ∀ᶠ parameter : ℕ in atTop, ∀ target : ℤ,
      |(target : ℝ)| ≤ 3 * fixedOrder * (parameter : ℝ) ^ 2 →
      rootSumError (v7RootWidth parameter) (v7RootThetaBound parameter) (cutoff parameter)
        (count parameter - 1) target ≤ v7RootErrorBound parameter := by
  have hN := AFT.negligible_polynomial_stretched_exponential
    8 60 2 (4 * Real.pi) (by norm_num) (by norm_num) (by positivity)
  have hsmallPoly : ∀ᶠ parameter : ℕ in atTop,
      8 * (parameter : ℝ) ^ 60 * Real.exp (-4 * Real.pi * (parameter : ℝ) ^ 2) ≤ 1 := by
    filter_upwards [hN 0] with parameter h
    have h' := (le_abs_self _).trans h
    simpa only [pow_zero, div_one, Real.rpow_two, neg_mul] using h'
  have hlarge : ∀ᶠ parameter : ℕ in atTop, 9 * Real.pi * (fixedOrder : ℝ) ^ 2 ≤ 8 * parameter := by
    have ht : Tendsto (fun parameter : ℕ => (parameter : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_ge_atTop (9 * Real.pi * (fixedOrder : ℝ) ^ 2 / 8))]
      with parameter hp
    linarith
  filter_upwards [hcountL, hcountU, hcutoff, hsmallPoly, hlarge, eventually_ge_atTop 1]
    with parameter hcL hcU hcut hsmall hlarge hp
  intro target htarget
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < parameter := zero_lt_one.trans_le hp'
  have hcpos : 0 < count parameter := (pow_pos (by omega : 0 < parameter) 3).trans_le hcL
  have hcEq : count parameter - 1 + 1 = count parameter := Nat.sub_add_cancel hcpos
  have hcL' : (parameter : ℝ) ^ 3 ≤ count parameter := by exact_mod_cast hcL
  have hcU' : (count parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 60 := by exact_mod_cast hcU
  have hcut' : 2 * (parameter : ℝ) ^ 2 ≤ cutoff parameter := by exact_mod_cast hcut
  have hw : 0 < v7RootWidth parameter := by unfold v7RootWidth; positivity
  have he0 : 0 ≤ v7RootThetaBound parameter := by unfold v7RootThetaBound; positivity
  have hsmall' : (count parameter : ℝ) * v7RootThetaBound parameter ≤ 1 := by
    apply le_trans _ hsmall
    unfold v7RootThetaBound
    have hh := mul_le_mul_of_nonneg_right hcU'
      (by positivity : 0 ≤ 4 * Real.exp (-4 * Real.pi * (parameter : ℝ) ^ 2))
    convert hh using 1
    ring
  have he1 : v7RootThetaBound parameter ≤ 1 := by
    have hc1 : (1 : ℝ) ≤ count parameter := by exact_mod_cast hcpos
    nlinarith
  have hcenter : Real.pi * (target : ℝ) ^ 2 ≤
      powerWidth (v7RootWidth parameter) (count parameter - 1) ^ 2 := by
    rw [powerWidth_sq, hcEq, v7RootWidth_sq]
    have hsq : (target : ℝ) ^ 2 ≤ (3 * fixedOrder * (parameter : ℝ) ^ 2) ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (target : ℝ)) (by positivity)).mpr htarget
      simpa only [sq_abs] using hh
    calc
      _ ≤ Real.pi * (3 * fixedOrder * (parameter : ℝ) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
      _ = (9 * Real.pi * (fixedOrder : ℝ) ^ 2) * (parameter : ℝ) ^ 4 := by ring
      _ ≤ (8 * parameter) * (parameter : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = (parameter : ℝ) ^ 3 * (8 * (parameter : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcL' (by positivity)
  have hbound := v7_rootSumError_envelope parameter (cutoff parameter) (count parameter - 1)
    (target) hp (by simpa only [hcEq] using hcU') hcut'
    (by simpa only [hcEq] using hsmall') hcenter
  exact hbound

noncomputable def v7RootCutoff (parameter : ℕ) : ℕ := 3 * parameter ^ 2 - 1

theorem bodies_sub_fixed_lower_eventually (removed : ℕ) :
    ∀ᶠ parameter : ℕ in atTop, parameter ^ 3 ≤ AFT.Parameters.bodies parameter - removed := by
  filter_upwards [eventually_ge_atTop (max 2 removed)] with parameter hp
  have hp2 : 2 ≤ parameter := (le_max_left _ _).trans hp
  have hr : removed ≤ parameter := (le_max_right _ _).trans hp
  have hsec := AFT.Parameters.security_eq parameter hp2
  have hdim := (AFT.Parameters.dimension_bounds parameter).1
  rw [hsec] at hdim
  have hpop := AFT.Parameters.population_identity parameter
  have hlegs := AFT.Parameters.legs_le_half_bodies parameter
  have hbody : parameter ^ 60 ≤ 2 * AFT.Parameters.bodies parameter := by omega
  have h57 : 4 ≤ parameter ^ 57 := by
    have hh := Nat.pow_le_pow_left hp2 57
    omega
  have hcube : 4 * parameter ^ 3 ≤ parameter ^ 60 := by
    calc
      _ ≤ parameter ^ 57 * parameter ^ 3 := Nat.mul_le_mul_right _ h57
      _ = _ := by rw [← pow_add]
  have hp3 : parameter ≤ parameter ^ 3 := by
    have hh := pow_le_pow_right₀ (by omega : 1 ≤ parameter) (by decide : 1 ≤ 3)
    simpa using hh
  omega

theorem bodies_sub_fixed_upper_eventually (removed : ℕ) :
    ∀ᶠ parameter : ℕ in atTop, AFT.Parameters.bodies parameter - removed ≤ 2 * parameter ^ 60 := by
  filter_upwards [eventually_ge_atTop 2] with parameter hp
  have hdim := (AFT.Parameters.dimension_bounds parameter).2
  rw [AFT.Parameters.security_eq parameter hp] at hdim
  exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hdim)

theorem v7RootCutoff_lower_eventually :
    ∀ᶠ parameter : ℕ in atTop, 2 * parameter ^ 2 ≤ v7RootCutoff parameter := by
  filter_upwards [eventually_ge_atTop 1] with parameter hp
  have hp2 : 1 ≤ parameter ^ 2 := one_le_pow₀ hp
  unfold v7RootCutoff
  omega

/-- The actual V7 population, scalar width and cutoff satisfy the complete
negligible relative convolution estimate. This covers `N`, `N-1`, and
`N-k`, for every fixed `k`, uniformly over the stated protected centers. -/
theorem v7_bodies_rootSumError_negligible (removed fixedOrder : ℕ) (target : ℕ → ℤ)
    (htarget : ∀ᶠ parameter : ℕ in atTop,
      |(target parameter : ℝ)| ≤ 3 * fixedOrder * (parameter : ℝ) ^ 2) :
    AFT.Negligible (fun parameter => rootSumError (v7RootWidth parameter)
      (v7RootThetaBound parameter) (v7RootCutoff parameter)
      (AFT.Parameters.bodies parameter - removed - 1) (target parameter)) :=
  v7_rootSumError_negligible fixedOrder (fun parameter => AFT.Parameters.bodies parameter - removed)
    v7RootCutoff target (bodies_sub_fixed_lower_eventually removed)
    (bodies_sub_fixed_upper_eventually removed) v7RootCutoff_lower_eventually htarget

/-- Uniform centerwise error for the actual V7 body population. -/
theorem v7_bodies_rootSumError_envelope_eventually (removed fixedOrder : ℕ) :
    ∀ᶠ parameter : ℕ in atTop, ∀ target : ℤ,
      |(target : ℝ)| ≤ 3 * fixedOrder * (parameter : ℝ) ^ 2 →
      rootSumError (v7RootWidth parameter) (v7RootThetaBound parameter) (v7RootCutoff parameter)
        (AFT.Parameters.bodies parameter - removed - 1) target ≤ v7RootErrorBound parameter :=
  v7_rootSumError_uniform_envelope fixedOrder (fun parameter => AFT.Parameters.bodies parameter - removed)
    v7RootCutoff (bodies_sub_fixed_lower_eventually removed)
    (bodies_sub_fixed_upper_eventually removed) v7RootCutoff_lower_eventually

end AFT.GaussianSource

import AFT.GaussianTail

/-!
# Uniform theta estimates and genuine integer Gaussian convolution

The shifted theta identity is obtained from mathlib's Gaussian Poisson
summation formula.  Its error bound is uniform over every real center.
All convolution masses in this file are sums over the actual integer lattice.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable def shiftedWeight (width center : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-(Real.pi / width ^ 2) * ((z : ℝ) - center) ^ 2)

noncomputable def theta (width center : ℝ) : ℝ :=
  ∑' z : ℤ, shiftedWeight width center z

noncomputable def thetaFourier (width center : ℝ) (z : ℤ) : ℂ :=
  Complex.exp (-Real.pi * (width : ℂ) ^ 2 * (z : ℂ) ^ 2 +
    2 * Real.pi * Complex.I * center * z)

/-- Poisson summation for an arbitrarily shifted integer lattice. -/
theorem theta_poisson (width center : ℝ) (hw : 0 < width) :
    (theta width center : ℂ) / width = ∑' z : ℤ, thetaFourier width center z := by
  have hs : ((width : ℂ) ^ 2) ^ (1 / 2 : ℂ) = width := by
    have hr : (width ^ 2) ^ (1 / 2 : ℝ) = width := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hw.le]
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    dsimp only at hc
    rw [Complex.ofReal_cpow (sq_nonneg width)] at hc
    simpa using hc
  have hp := Complex.tsum_exp_neg_quadratic
    (a := (width : ℂ) ^ 2) (by simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_pos_of_pos hw)
    (Complex.I * center)
  rw [hs] at hp
  have hleft : (∑' z : ℤ, Complex.exp (-Real.pi * (width : ℂ) ^ 2 * z ^ 2 +
      2 * Real.pi * (Complex.I * center) * z)) =
      ∑' z : ℤ, thetaFourier width center z := by
    apply tsum_congr
    intro z
    congr 1
    ring
  have hright : (∑' z : ℤ, Complex.exp
      (-Real.pi / (width : ℂ) ^ 2 * (z + Complex.I * (Complex.I * center)) ^ 2)) =
      (theta width center : ℂ) := by
    rw [theta, Complex.ofReal_tsum]
    apply tsum_congr
    intro z
    rw [shiftedWeight, Complex.ofReal_exp]
    congr 1
    push_cast
    have hI : Complex.I * (Complex.I * (center : ℂ)) = -(center : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    rw [hI]
    ring
  rw [hleft, hright] at hp
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hp.symm

theorem thetaFourier_norm (width center : ℝ) (hw : 0 < width) (z : ℤ) :
    ‖thetaFourier width center z‖ = weight (1 / width) z := by
  rw [thetaFourier, Complex.norm_exp]
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.neg_re ]
  unfold weight
  congr 1
  field_simp

theorem summable_thetaFourier (width center : ℝ) (hw : 0 < width) :
    Summable (thetaFourier width center) := by
  apply Summable.of_norm
  simpa only [thetaFourier_norm width center hw] using summable_weight (1 / width) (by positivity)

/-- The nonzero Fourier modes control the entire relative error, uniformly
in the center, by the zero-centered dual Gaussian mass. -/
theorem theta_relative_error (width center : ℝ) (hw : 0 < width) :
    |theta width center / width - 1| ≤ realNormalizer (1 / width) - 1 := by
  let f := thetaFourier width center
  have hf := summable_thetaFourier width center hw
  have hnorm : Summable (fun z : ℤ => ‖if z = 0 then (0 : ℂ) else f z‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (summable_weight (1 / width) (by positivity))
    intro z
    split_ifs
    · exact (show ‖(0 : ℂ)‖ = 0 by norm_num).symm ▸ (weight_pos (1 / width) z).le
    · exact le_of_eq (thetaFourier_norm width center hw z)
  have hzero : f 0 = 1 := by simp [f, thetaFourier]
  have heq := hf.tsum_eq_add_tsum_ite (0 : ℤ)
  change (∑' z : ℤ, f z) = f 0 + ∑' z : ℤ, if z = 0 then 0 else f z at heq
  rw [hzero] at heq
  have hdual := (summable_weight (1 / width) (by positivity)).tsum_eq_add_tsum_ite (0 : ℤ)
  change realNormalizer (1 / width) = weight (1 / width) 0 + _ at hdual
  have hwzero : weight (1 / width) 0 = 1 := by simp [weight]
  rw [hwzero] at hdual
  have hnormsum : (∑' z : ℤ, ‖if z = 0 then (0 : ℂ) else f z‖) =
      realNormalizer (1 / width) - 1 := by
    have heq' : (∑' z : ℤ, ‖if z = 0 then (0 : ℂ) else f z‖) =
        ∑' z : ℤ, if z = 0 then 0 else weight (1 / width) z := by
      apply tsum_congr
      intro z
      split_ifs
      · exact norm_zero
      · exact thetaFourier_norm width center hw z
    rw [heq']
    linarith
  have hcomplex : ((theta width center / width - 1 : ℝ) : ℂ) =
      ∑' z : ℤ, if z = 0 then 0 else f z := by
    push_cast
    rw [theta_poisson width center hw]
    change (∑' z : ℤ, f z) - 1 = _
    rw [heq]
    ring
  have h := norm_tsum_le_tsum_norm hnorm
  rw [← hcomplex, Complex.norm_real, Real.norm_eq_abs, hnormsum] at h
  exact h

/-- Explicit exponentially small theta error. -/
noncomputable def thetaError (width : ℝ) : ℝ :=
  2 * (Real.exp (-Real.pi * width ^ 2) / (1 - Real.exp (-Real.pi * width ^ 2)))

theorem thetaError_nonneg (width : ℝ) (hw : 0 < width) : 0 ≤ thetaError width := by
  have h : Real.exp (-Real.pi * width ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hw])
  exact mul_nonneg (by norm_num) (div_nonneg (Real.exp_pos _).le (by linarith))

theorem theta_relative_error_exp (width center : ℝ) (hw : 0 < width) :
    |theta width center / width - 1| ≤ thetaError width := by
  apply (theta_relative_error width center hw).trans
  have h := realNormalizer_le_geometric (1 / width) (by positivity)
  have heq : Real.pi / (1 / width) ^ 2 = Real.pi * width ^ 2 := by field_simp
  rw [heq, ← neg_mul] at h
  unfold thetaError
  linarith

theorem summable_shiftedWeight (width center : ℝ) (hw : 0 < width) :
    Summable (shiftedWeight width center) := by
  let coefficient := Real.pi / width ^ 2
  have hc : 0 < coefficient := div_pos Real.pi_pos (sq_pos_of_pos hw)
  have hw' : 0 < Real.sqrt 2 * width := by positivity
  apply Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) _
    ((summable_weight (Real.sqrt 2 * width) hw').mul_left
      (Real.exp (coefficient * center ^ 2)))
  intro z
  unfold weight
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq := mul_nonneg hc.le (sq_nonneg ((z : ℝ) - 2 * center))
  change -coefficient * ((z : ℝ) - center) ^ 2 ≤ _
  have heq : coefficient * center ^ 2 + -(Real.pi / (2 * width ^ 2)) * (z : ℝ) ^ 2 =
      coefficient * center ^ 2 - coefficient * (z : ℝ) ^ 2 / 2 := by
    dsimp [coefficient]
    ring
  rw [heq]
  nlinarith

theorem theta_pos (width center : ℝ) (hw : 0 < width) : 0 < theta width center := by
  apply (Real.exp_pos (-(Real.pi / width ^ 2) * (0 - center) ^ 2)).trans_le
  convert (summable_shiftedWeight width center hw).le_tsum (0 : ℤ)
    (fun z _ => (Real.exp_pos _).le) using 1
  simp [shiftedWeight]

noncomputable def sumWidth (left right : ℝ) : ℝ := Real.sqrt (left ^ 2 + right ^ 2)
noncomputable def harmonicWidth (left right : ℝ) : ℝ := left * right / sumWidth left right
noncomputable def convolutionCenter (left right : ℝ) (target : ℤ) : ℝ :=
  left ^ 2 * (target : ℝ) / (left ^ 2 + right ^ 2)

 theorem sumWidth_pos (left right : ℝ) (hl : 0 < left) (hr : 0 < right) :
    0 < sumWidth left right := by unfold sumWidth; positivity

theorem harmonicWidth_pos (left right : ℝ) (hl : 0 < left) (hr : 0 < right) :
    0 < harmonicWidth left right := div_pos (mul_pos hl hr) (sumWidth_pos left right hl hr)

/-- The precise completion of the square, including its lattice center. -/
theorem convolution_weight_factor (left right : ℝ) (hl : 0 < left) (hr : 0 < right)
    (target z : ℤ) :
    weight left z * weight right (target - z) =
      weight (sumWidth left right) target *
        shiftedWeight (harmonicWidth left right) (convolutionCenter left right target) z := by
  have hsum : 0 < left ^ 2 + right ^ 2 := by positivity
  have hsumSq : sumWidth left right ^ 2 = left ^ 2 + right ^ 2 :=
    Real.sq_sqrt hsum.le
  have hharmSq : harmonicWidth left right ^ 2 = left ^ 2 * right ^ 2 /
      (left ^ 2 + right ^ 2) := by
    rw [harmonicWidth, div_pow, mul_pow, hsumSq]
  unfold weight shiftedWeight convolutionCenter
  rw [hsumSq, hharmSq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- Unnormalized convolution on the infinite integer lattice. -/
noncomputable def convolutionWeight (left right : ℝ) (target : ℤ) : ℝ :=
  ∑' z : ℤ, weight left z * weight right (target - z)

/-- Every two-input convolution is a continuum Gaussian multiplied by
one exact shifted theta factor. -/
theorem convolutionWeight_eq (left right : ℝ) (hl : 0 < left) (hr : 0 < right)
    (target : ℤ) :
    convolutionWeight left right target = weight (sumWidth left right) target *
      theta (harmonicWidth left right) (convolutionCenter left right target) := by
  unfold convolutionWeight
  simp_rw [convolution_weight_factor left right hl hr]
  exact tsum_mul_left

/-- The local Gaussian approximation has a fully explicit uniform relative
error, with no restriction on the integer output value. -/
theorem convolutionWeight_relative_error (left right : ℝ) (hl : 0 < left) (hr : 0 < right)
    (target : ℤ) :
    |convolutionWeight left right target /
        (harmonicWidth left right * weight (sumWidth left right) target) - 1| ≤
      thetaError (harmonicWidth left right) := by
  rw [convolutionWeight_eq left right hl hr]
  have hweight := (weight_pos (sumWidth left right) target).ne'
  have hratio : weight (sumWidth left right) target *
      theta (harmonicWidth left right) (convolutionCenter left right target) /
      (harmonicWidth left right * weight (sumWidth left right) target) =
      theta (harmonicWidth left right) (convolutionCenter left right target) /
        harmonicWidth left right := by field_simp
  rw [hratio]
  exact theta_relative_error_exp _ _ (harmonicWidth_pos left right hl hr)

/-- Convolution of the actual normalized integer-Gaussian probability
masses, using precisely the PMFs from `GaussianSource`. -/
noncomputable def convolutionProbability (left right : ℝ) (hl : 0 < left) (hr : 0 < right)
    (target : ℤ) : ℝ :=
  ∑' z : ℤ, (integerGaussian left hl z).toReal *
    (integerGaussian right hr (target - z)).toReal

theorem convolutionProbability_eq (left right : ℝ) (hl : 0 < left) (hr : 0 < right)
    (target : ℤ) :
    convolutionProbability left right hl hr target =
      convolutionWeight left right target / (realNormalizer left * realNormalizer right) := by
  unfold convolutionProbability convolutionWeight
  rw [← tsum_div_const]
  apply tsum_congr
  intro z
  rw [integerGaussian_toReal, integerGaussian_toReal]
  ring

theorem convolutionProbability_relative_error (left right : ℝ) (hl : 0 < left) (hr : 0 < right)
    (target : ℤ) :
    |convolutionProbability left right hl hr target /
        (harmonicWidth left right * weight (sumWidth left right) target /
          (realNormalizer left * realNormalizer right)) - 1| ≤
      thetaError (harmonicWidth left right) := by
  rw [convolutionProbability_eq]
  have hnormalizer : realNormalizer left * realNormalizer right ≠ 0 :=
    (mul_pos (lt_of_lt_of_le zero_lt_one (realNormalizer_ge_one left hl))
      (lt_of_lt_of_le zero_lt_one (realNormalizer_ge_one right hr))).ne'
  rw [div_div_div_cancel_right₀ hnormalizer]
  exact convolutionWeight_relative_error left right hl hr target

/-- The theta error decreases with the Gaussian width. -/
theorem thetaError_antitone (left right : ℝ) (hl : 0 < left) (h : left ≤ right) :
    thetaError right ≤ thetaError left := by
  have hr : 0 < right := hl.trans_le h
  have hl1 : Real.exp (-Real.pi * left ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hl])
  have hr1 : Real.exp (-Real.pi * right ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hr])
  have hsq : left ^ 2 ≤ right ^ 2 := (sq_le_sq₀ hl.le hr.le).mpr h
  have he : Real.exp (-Real.pi * right ^ 2) ≤ Real.exp (-Real.pi * left ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  unfold thetaError
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - Real.exp (-Real.pi * right ^ 2))
    (by linarith : 0 < 1 - Real.exp (-Real.pi * left ^ 2))).mpr
  nlinarith

theorem thetaError_le_four_exp (width : ℝ) (hw : 1 ≤ width) :
    thetaError width ≤ 4 * Real.exp (-Real.pi * width ^ 2) := by
  have hw0 : 0 < width := zero_lt_one.trans_le hw
  have hcoef : 1 ≤ Real.pi * width ^ 2 := by
    have hsq : 1 ≤ width ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have he : 2 ≤ Real.exp (Real.pi * width ^ 2) :=
    (by linarith : 2 ≤ Real.pi * width ^ 2 + 1).trans (Real.add_one_le_exp _)
  have hhalf : Real.exp (-Real.pi * width ^ 2) ≤ 1 / 2 := by
    rw [neg_mul, Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by simpa using he)
  have hden : 0 < 1 - Real.exp (-Real.pi * width ^ 2) := by linarith
  unfold thetaError
  have hquot : Real.exp (-Real.pi * width ^ 2) /
      (1 - Real.exp (-Real.pi * width ^ 2)) ≤ 2 * Real.exp (-Real.pi * width ^ 2) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.exp_pos (-Real.pi * width ^ 2)]
  linarith

noncomputable def gaussianKernel (width : ℝ) (z : ℤ) : ℝ := weight width z / width

theorem gaussianKernel_pos (width : ℝ) (hw : 0 < width) (z : ℤ) :
    0 < gaussianKernel width z := div_pos (weight_pos width z) hw

theorem summable_gaussianKernel (width : ℝ) (hw : 0 < width) :
    Summable (gaussianKernel width) := (summable_weight width hw).div_const width

theorem summable_kernel_product (left right : ℝ) (hl : 0 < left) (hr : 0 < right)
    (target : ℤ) :
    Summable (fun z : ℤ => gaussianKernel left z * gaussianKernel right (target - z)) := by
  have h := (summable_shiftedWeight (harmonicWidth left right)
    (convolutionCenter left right target) (harmonicWidth_pos left right hl hr)).mul_left
      (weight (sumWidth left right) target / (left * right))
  apply h.congr
  intro z
  rw [gaussianKernel, gaussianKernel, div_mul_div_comm, convolution_weight_factor left right hl hr]
  ring

theorem kernel_convolution_eq (left right : ℝ) (hl : 0 < left) (hr : 0 < right)
    (target : ℤ) :
    (∑' z : ℤ, gaussianKernel left z * gaussianKernel right (target - z)) =
      gaussianKernel (sumWidth left right) target *
        (theta (harmonicWidth left right) (convolutionCenter left right target) /
          harmonicWidth left right) := by
  unfold gaussianKernel
  simp_rw [div_mul_div_comm]
  rw [tsum_div_const]
  change convolutionWeight left right target / (left * right) = _
  rw [convolutionWeight_eq left right hl hr, harmonicWidth]
  field_simp [(sumWidth_pos left right hl hr).ne']

/-- Every merge of input widths at least `base` has harmonic width at
least `base / sqrt 2`. This also covers a sequential convolution tree. -/
theorem harmonicWidth_lower (base left right : ℝ) (hb : 0 < base)
    (hl : base ≤ left) (hr : base ≤ right) :
    base / Real.sqrt 2 ≤ harmonicWidth left right := by
  have hl0 : 0 < left := hb.trans_le hl
  have hr0 : 0 < right := hb.trans_le hr
  have hl2 : base ^ 2 ≤ left ^ 2 := (sq_le_sq₀ hb.le hl0.le).mpr hl
  have hr2 : base ^ 2 ≤ right ^ 2 := (sq_le_sq₀ hb.le hr0.le).mpr hr
  have hsum : 0 < left ^ 2 + right ^ 2 := by positivity
  apply (sq_le_sq₀ (by positivity : 0 ≤ base / Real.sqrt 2)
    (harmonicWidth_pos left right hl0 hr0).le).mp
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), harmonicWidth,
    div_pow, mul_pow, sumWidth, Real.sq_sqrt hsum.le]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsum).mpr
  nlinarith [mul_nonneg (sq_nonneg left) (sub_nonneg.mpr hr2),
    mul_nonneg (sq_nonneg right) (sub_nonneg.mpr hl2)]

/-- The width after `merges + 1` independent equal-width inputs. -/
noncomputable def powerWidth (width : ℝ) : ℕ → ℝ
  | 0 => width
  | n + 1 => sumWidth (powerWidth width n) width

theorem powerWidth_pos (width : ℝ) (hw : 0 < width) (n : ℕ) : 0 < powerWidth width n := by
  induction n with
  | zero => exact hw
  | succ n ih => exact sumWidth_pos _ _ ih hw

theorem powerWidth_ge (width : ℝ) (n : ℕ) : width ≤ powerWidth width n := by
  cases n with
  | zero => rfl
  | succ n =>
    change width ≤ Real.sqrt (powerWidth width n ^ 2 + width ^ 2)
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (powerWidth width n)])

theorem powerWidth_sq (width : ℝ) (n : ℕ) :
    powerWidth width n ^ 2 = (n + 1 : ℕ) * width ^ 2 := by
  induction n with
  | zero => simp [powerWidth]
  | succ n ih =>
    rw [powerWidth, sumWidth, Real.sq_sqrt (by positivity), ih]
    push_cast
    ring

theorem powerWidth_eq (width : ℝ) (hw : 0 < width) (n : ℕ) :
    powerWidth width n = Real.sqrt (n + 1 : ℕ) * width := by
  apply (sq_eq_sq₀ (powerWidth_pos width hw n).le (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), powerWidth_sq]

/-- Recursive integer convolution of the continuum-normalized initial
Gaussian kernel. The first index is the number of merges, so there are
`merges + 1` genuine input variables. -/
noncomputable def kernelPower (width : ℝ) : ℕ → ℤ → ℝ
  | 0 => gaussianKernel width
  | n + 1 => fun target => ∑' z : ℤ, kernelPower width n z * gaussianKernel width (target - z)

theorem kernelPower_nonneg (width : ℝ) (hw : 0 < width) (n : ℕ) (target : ℤ) :
    0 ≤ kernelPower width n target := by
  induction n generalizing target with
  | zero => exact (gaussianKernel_pos width hw target).le
  | succ n ih => exact tsum_nonneg (fun z => mul_nonneg (ih z) (gaussianKernel_pos width hw _).le)

/-- Explicit multiplicative accumulation of the theta errors over every
merge. There is no assumed Gaussian approximation in the induction. -/
theorem kernelPower_bounds (width error : ℝ) (hw : 0 < width)
    (he0 : 0 ≤ error) (he1 : error ≤ 1)
    (he : thetaError (width / Real.sqrt 2) ≤ error) (n : ℕ) (target : ℤ) :
    (1 - error) ^ n * gaussianKernel (powerWidth width n) target ≤ kernelPower width n target ∧
    kernelPower width n target ≤ (1 + error) ^ n * gaussianKernel (powerWidth width n) target := by
  induction n generalizing target with
  | zero => simp [kernelPower, powerWidth]
  | succ n ih =>
    have hwidth := powerWidth_pos width hw n
    have hbase : 0 < width / Real.sqrt 2 := by positivity
    have hharm := harmonicWidth_lower width (powerWidth width n) width hw (powerWidth_ge width n) le_rfl
    have htheta := (theta_relative_error_exp (harmonicWidth (powerWidth width n) width)
      (convolutionCenter (powerWidth width n) width target)
      (harmonicWidth_pos _ _ hwidth hw)).trans
      ((thetaError_antitone _ _ hbase hharm).trans he)
    have htheta' := abs_le.mp htheta
    let ratio := theta (harmonicWidth (powerWidth width n) width)
      (convolutionCenter (powerWidth width n) width target) /
      harmonicWidth (powerWidth width n) width
    have hratioL : 1 - error ≤ ratio := by dsimp [ratio]; linarith [htheta'.1]
    have hratioU : ratio ≤ 1 + error := by dsimp [ratio]; linarith [htheta'.2]
    have hprod := summable_kernel_product (powerWidth width n) width hwidth hw target
    have hactual : Summable (fun z : ℤ => kernelPower width n z * gaussianKernel width (target - z)) := by
      apply Summable.of_nonneg_of_le
        (fun z => mul_nonneg (kernelPower_nonneg width hw n z) (gaussianKernel_pos width hw _).le) _
        (hprod.mul_left ((1 + error) ^ n))
      intro z
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (ih z).2
        (gaussianKernel_pos width hw (target - z)).le
    have hL := (hprod.mul_left ((1 - error) ^ n)).tsum_le_tsum
      (fun z => by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (ih z).1
          (gaussianKernel_pos width hw (target - z)).le) hactual
    have hU := hactual.tsum_le_tsum
      (fun z => by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (ih z).2
          (gaussianKernel_pos width hw (target - z)).le) (hprod.mul_left ((1 + error) ^ n))
    rw [tsum_mul_left, kernel_convolution_eq _ _ hwidth hw] at hL hU
    have hg := (gaussianKernel_pos (sumWidth (powerWidth width n) width)
      (sumWidth_pos _ _ hwidth hw) target).le
    constructor
    · change _ ≤ ∑' z : ℤ, kernelPower width n z * gaussianKernel width (target - z)
      apply le_trans _ hL
      change (1 - error) ^ (n + 1) * gaussianKernel (sumWidth (powerWidth width n) width) target ≤
        (1 - error) ^ n * (gaussianKernel (sumWidth (powerWidth width n) width) target * ratio)
      have h := mul_le_mul_of_nonneg_left hratioL (mul_nonneg (pow_nonneg (by linarith : 0 ≤ 1 - error) n) hg)
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
    · change (∑' z : ℤ, kernelPower width n z * gaussianKernel width (target - z)) ≤ _
      apply le_trans hU
      change (1 + error) ^ n * (gaussianKernel (sumWidth (powerWidth width n) width) target * ratio) ≤
        (1 + error) ^ (n + 1) * gaussianKernel (sumWidth (powerWidth width n) width) target
      have h := mul_le_mul_of_nonneg_left hratioU (mul_nonneg (pow_nonneg (by linarith : 0 ≤ 1 + error) n) hg)
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

end AFT.GaussianSource

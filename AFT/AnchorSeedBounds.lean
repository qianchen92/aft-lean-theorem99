import AFT.ActualBodyCenter

/-! # Finite anchor smoothing bounds for the genuine safe seed -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

variable {Input Output : Type*} [Fintype Input] [Fintype Output]

def positiveKernelMap (kernel : Input → Output → ℝ) (profile : Input → ℝ) : Output → ℝ :=
  fun output => ∑ input, profile input * kernel input output

theorem positiveKernelMap_l1_le (kernel : Input → Output → ℝ) (profile : Input → ℝ)
    (hk : ∀ i o, 0 ≤ kernel i o) (hm : ∀ i, (∑ o, kernel i o) ≤ 1) :
    (∑ o, |positiveKernelMap kernel profile o|) ≤ ∑ i, |profile i| := by
  calc
    _ ≤ ∑ o, ∑ i, |profile i| * kernel i o := by
      apply Finset.sum_le_sum
      intro o _
      simpa only [positiveKernelMap, abs_mul, abs_of_nonneg (hk _ _)] using
        Finset.abs_sum_le_sum_abs (fun i => profile i * kernel i o) Finset.univ
    _ ≤ _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (mul_le_mul_of_nonneg_left (hm i) (abs_nonneg (profile i))).trans_eq (mul_one _)

omit [Fintype Output] in
theorem positiveKernelMap_sup_le (kernel : Input → Output → ℝ) (profile : Input → ℝ) (bound : ℝ)
    (hk : ∀ i o, 0 ≤ kernel i o) (hb : ∀ i o, kernel i o ≤ bound) (o : Output) :
    |positiveKernelMap kernel profile o| ≤ bound * ∑ i, |profile i| := by
  calc
    _ ≤ ∑ i, |profile i| * kernel i o := by
      simpa only [positiveKernelMap, abs_mul, abs_of_nonneg (hk _ _)] using
        Finset.abs_sum_le_sum_abs (fun i => profile i * kernel i o) Finset.univ
    _ ≤ ∑ i, |profile i| * bound := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i o) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The actual row mass and pointwise kernel bound imply the sharp
L1-to-counting-L2 smoothing estimate. -/
theorem positiveKernelMap_l2Sq_le (kernel : Input → Output → ℝ) (profile : Input → ℝ) (bound : ℝ)
    (hk : ∀ i o, 0 ≤ kernel i o) (hm : ∀ i, (∑ o, kernel i o) ≤ 1)
    (hb0 : 0 ≤ bound) (hb : ∀ i o, kernel i o ≤ bound) :
    (∑ o, positiveKernelMap kernel profile o ^ 2) ≤ bound * (∑ i, |profile i|) ^ 2 := by
  calc
    _ ≤ ∑ o, (bound * ∑ i, |profile i|) * |positiveKernelMap kernel profile o| := by
      apply Finset.sum_le_sum
      intro o _
      have hh := mul_le_mul_of_nonneg_right (positiveKernelMap_sup_le kernel profile bound hk hb o)
        (abs_nonneg (positiveKernelMap kernel profile o))
      nlinarith only [hh, sq_abs (positiveKernelMap kernel profile o)]
    _ ≤ (bound * ∑ i, |profile i|) * ∑ i, |profile i| := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (positiveKernelMap_l1_le kernel profile hk hm)
        (mul_nonneg hb0 (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    _ = _ := by ring

theorem positiveKernelMap_mass (kernel : Input → Output → ℝ) (profile : Input → ℝ)
    (hm : ∀ i, (∑ o, kernel i o) = 1) :
    (∑ o, positiveKernelMap kernel profile o) = ∑ i, profile i := by
  unfold positiveKernelMap
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hm, mul_one]

omit [Fintype Output] in
theorem positiveKernelMap_sub (kernel : Input → Output → ℝ) (first second : Input → ℝ) :
    positiveKernelMap kernel (first - second) = positiveKernelMap kernel first - positiveKernelMap kernel second := by
  funext o
  simp only [positiveKernelMap, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- A nonnegative probability kernel close in input L1 to uniform gives a
small squared safe seed, retaining the anchor smoothing gain. -/
theorem positiveKernelMap_seed_l2Sq (kernel : Input → Output → ℝ) (primary uniform : Input → ℝ)
    (core : Output → ℝ) (bound baseline : ℝ)
    (hk : ∀ i o, 0 ≤ kernel i o) (hm : ∀ i, (∑ o, kernel i o) = 1)
    (hb0 : 0 ≤ bound) (hb : ∀ i o, kernel i o ≤ bound)
    (hu : ∀ i, 0 ≤ uniform i) (hum : ∑ i, uniform i = 1)
    (hc : ∀ o, 0 ≤ core o) (hcm : ∑ o, core o = 1)
    (hbase : ∀ o, positiveKernelMap kernel uniform o ≤ baseline ∧ core o ≤ baseline) :
    (∑ o, (positiveKernelMap kernel primary o - core o) ^ 2) ≤
      2 * bound * (∑ i, |primary i - uniform i|) ^ 2 + 4 * baseline := by
  let U := positiveKernelMap kernel uniform
  have hU0 (o) : 0 ≤ U o := Finset.sum_nonneg fun i _ => mul_nonneg (hu i) (hk i o)
  have hUm : ∑ o, U o = 1 := (positiveKernelMap_mass kernel uniform hm).trans hum
  have hbaseSq : (∑ o, (U o - core o) ^ 2) ≤ 2 * baseline := by
    calc
      _ ≤ ∑ o, baseline * (U o + core o) := by
        apply Finset.sum_le_sum
        intro o _
        have hh := hbase o
        have hx := hU0 o
        have hy := hc o
        change U o ≤ baseline ∧ core o ≤ baseline at hh
        nlinarith
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, hUm, hcm]; ring
  have hdiff := positiveKernelMap_l2Sq_le kernel (primary - uniform) bound hk (fun i => (hm i).le) hb0 hb
  rw [positiveKernelMap_sub] at hdiff
  calc
    _ ≤ ∑ o, (2 * (positiveKernelMap kernel primary o - U o) ^ 2 + 2 * (U o - core o) ^ 2) := by
      apply Finset.sum_le_sum
      intro o _
      nlinarith [sq_nonneg (positiveKernelMap kernel primary o - U o - (U o - core o))]
    _ ≤ _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Pi.sub_apply] at hdiff
      linarith

namespace V7Calibration
open Filter GaussianSource
open scoped Topology

theorem safePalette_card (parameter : ℕ) : (safePalette parameter).card = Parameters.safeSize parameter := by
  unfold safePalette Parameters.safeSize
  rw [TrimmedSlice.paletteSlice_card _ _ _ (by positivity)]
  simp only [abs_zero, sub_zero]
  omega

theorem safeMargin_quarter (parameter : ℕ) : 4 * Parameters.safeMargin parameter ≤ Parameters.modulus parameter := by
  have hh : 80 ≤ Parameters.security parameter ^ 38 := by
    have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 38
    omega
  have hmul := Nat.mul_le_mul_right (Parameters.security parameter ^ 2) hh
  have hm : 4 * Parameters.safeMargin parameter ≤ Parameters.security parameter ^ 40 := by
    convert hmul using 1 <;> simp [Parameters.safeMargin, ← pow_add, ← Nat.mul_assoc]
  exact hm.trans (Parameters.modulus_bounds parameter).1

theorem actualCoreLaw_bounds (parameter : ℕ) :
    (∀ color, (actualCoreLaw parameter).weight color ≤ 2 / (Parameters.modulus parameter : ℝ)) ∧
    (∀ color ∈ safePalette parameter, 1 / (Parameters.modulus parameter : ℝ) ≤ (actualCoreLaw parameter).weight color) := by
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hc : (0 : ℝ) < (safePalette parameter).card := by exact_mod_cast (safePalette_nonempty parameter).card_pos
  have hlow : (Parameters.modulus parameter : ℝ) / 2 ≤ (safePalette parameter).card := by
    have hm := safeMargin_quarter parameter
    have heq := safePalette_card parameter
    unfold Parameters.safeSize at heq
    have hh : Parameters.modulus parameter ≤ 2 * (safePalette parameter).card := by omega
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa only [mul_comm] using (show (Parameters.modulus parameter : ℝ) ≤ 2 * (safePalette parameter).card by exact_mod_cast hh))
  have hhigh : ((safePalette parameter).card : ℝ) ≤ Parameters.modulus parameter := by
    exact_mod_cast (show (safePalette parameter).card ≤ Parameters.modulus parameter by simpa only [Fintype.card_fin] using Finset.card_le_univ (safePalette parameter))
  constructor
  · intro color
    rw [actualCoreLaw_weight]
    unfold uniformFiniteProfile
    split_ifs
    · have hh := one_div_le_one_div_of_le (by positivity : 0 < (Parameters.modulus parameter : ℝ) / 2) hlow
      rw [one_div_div] at hh
      simpa only [one_div] using hh
    · positivity
  · intro color hin
    rw [actualCoreLaw_weight]
    simpa only [uniformFiniteProfile, if_pos hin, one_div] using one_div_le_one_div_of_le hc hhigh

def extraAnchorSeed (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) : Fin (Parameters.modulus parameter) → ℝ :=
  fun center => blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (extraShift cutoffScale parameter) (extraBlur cutoffScale parameter)
    (actualPrimary cutoffScale parameter beta) center.val - (actualCoreLaw parameter).weight center

/-- The actual safe seed keeps the full squared L1-to-L2 smoothing gain. -/
theorem actual_extra_anchor_seed_bounds (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∑ center, extraAnchorSeed cutoffScale parameter (beta parameter) center) = 0 ∧
      (∀ center, center ∉ safePalette parameter → extraAnchorSeed cutoffScale parameter (beta parameter) center = 0) ∧
      profileSquareNorm (actualBodyCenter cutoffScale parameter (beta parameter))
        (extraAnchorSeed cutoffScale parameter (beta parameter)) ≤
        4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter *
          (192 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8)) ^ 2 + 16 := by
  filter_upwards [actual_extra_anchor_safe_eventually cutoffScale hscale,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_uniform_l1_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta]
    with parameter hsafe hp hL1 hbody
  let kernel : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ :=
    fun color center => actualExtraAnchorKernel cutoffScale parameter color center.val
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let core := (actualCoreLaw parameter).weight
  let u : Fin (Parameters.modulus parameter) → ℝ := fun _ => 1 / (Parameters.modulus parameter : ℝ)
  let seed := extraAnchorSeed cutoffScale parameter (beta parameter)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hkernel (i o) : 0 ≤ kernel i o := blurredAnchorKernel_nonneg _ _ _ _ _ _
  have hmass (i) : (∑ o, kernel i o) = 1 := (hsafe i).1
  have hbound (i o) : kernel i o ≤ (Parameters.anchorWidth parameter : ℝ)⁻¹ := blurredAnchorKernel_le _ _ _ _ _ _
  have hum : ∑ i, u i = 1 := by simp [u, ne_of_gt hq]
  have hseed (o) : seed o = positiveKernelMap kernel p o - core o := rfl
  have huniform (o) : positiveKernelMap kernel u o ≤ 2 / (Parameters.modulus parameter : ℝ) := by
    unfold positiveKernelMap
    simp only [u, ← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left
      (blurredAnchorKernel_column_bound (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (extraShift cutoffScale parameter) (extraBlur cutoffScale parameter) o.val)
      (by positivity : 0 ≤ 1 / (Parameters.modulus parameter : ℝ))
    convert hh using 1; ring
  have hcount := positiveKernelMap_seed_l2Sq kernel p u core (Parameters.anchorWidth parameter : ℝ)⁻¹
    (2 / (Parameters.modulus parameter : ℝ)) hkernel hmass (by positivity) hbound
    (by intro; positivity) hum (actualCoreLaw parameter).nonneg (actualCoreLaw parameter).sum_one
    (fun o => ⟨huniform o, (actualCoreLaw_bounds parameter).1 o⟩)
  have hout (o) (ho : o ∉ safePalette parameter) : seed o = 0 := by
    rw [hseed]
    have hc : core o = 0 := by simp [core, actualCoreLaw, FiniteDist.uniformSafe, ho]
    rw [hc, sub_zero]
    unfold positiveKernelMap
    apply Finset.sum_eq_zero
    intro i _
    have hh : (o.val : ℤ) < Parameters.safeMargin parameter ∨
        (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter ≤ o.val := by
      simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
        TrimmedSlice.mem_slice] at ho
      omega
    exact mul_eq_zero_of_right _ ((hsafe i).2 o.val hh)
  have hnorm : profileSquareNorm (actualBodyCenter cutoffScale parameter (beta parameter)) seed ≤
      (2 * (Parameters.modulus parameter : ℝ)) * ∑ o, seed o ^ 2 := by
    unfold profileSquareNorm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro o _
    by_cases ho : o ∈ safePalette parameter
    · have hc := (actualCoreLaw_bounds parameter).2 o ho
      have hb := (hbody.2.1 o).1
      have hb0 : 0 < actualBodyCenter cutoffScale parameter (beta parameter) o := by
        exact lt_of_lt_of_le (by positivity : 0 < (1 / (Parameters.modulus parameter : ℝ)) / 2) (by linarith)
      apply (div_le_iff₀ hb0).mpr
      have hh : 1 ≤ (2 * (Parameters.modulus parameter : ℝ)) * actualBodyCenter cutoffScale parameter (beta parameter) o := by
        have hh : 1 / (Parameters.modulus parameter : ℝ) ≤ 2 * actualBodyCenter cutoffScale parameter (beta parameter) o := by linarith
        have hh' := (div_le_iff₀ hq).mp hh
        nlinarith
      have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (seed o))
      nlinarith only [hh']
    · rw [hout o ho]
      simp
  refine ⟨?_, hout, ?_⟩
  · change (∑ o, seed o) = 0
    simp_rw [hseed]
    rw [Finset.sum_sub_distrib, positiveKernelMap_mass kernel p hmass, hp.2, (actualCoreLaw parameter).sum_one]
    norm_num
  · have hsq := sq_le_sq₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) ((Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hL1.1) |>.mpr hL1.1
    have hcount' : (∑ o, seed o ^ 2) ≤
        2 * (Parameters.anchorWidth parameter : ℝ)⁻¹ * (192 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8)) ^ 2 +
          4 * (2 / (Parameters.modulus parameter : ℝ)) := by
      exact hcount.trans (add_le_add (mul_le_mul_of_nonneg_left hsq (by positivity)) le_rfl)
    apply hnorm.trans
    have hh := mul_le_mul_of_nonneg_left hcount' (by positivity : 0 ≤ 2 * (Parameters.modulus parameter : ℝ))
    convert hh using 1
    field_simp
    ring

def anchorSeedSquareConstant (cutoffScale : ℝ) : ℝ := 8 * (192 * activationConstant cutoffScale) ^ 2 + 16

/-- The original safe-seed exponents for the fully instantiated V7 model,
including the pointwise body-density bound used by fixed fibers. -/
theorem actual_extra_anchor_seed_power_bounds (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      profileSquareNorm (actualBodyCenter cutoffScale parameter (beta parameter))
        (extraAnchorSeed cutoffScale parameter (beta parameter)) ≤
        anchorSeedSquareConstant cutoffScale * (parameter : ℝ) ^ (1 / 2 : ℝ) ∧
      (∀ center, |extraAnchorSeed cutoffScale parameter (beta parameter) center| ≤
        (8 * (parameter : ℝ) ^ 8) * actualBodyCenter cutoffScale parameter (beta parameter) center) := by
  filter_upwards [actual_extra_anchor_seed_bounds cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hs hb hp hlarge
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hA : (Parameters.anchorWidth parameter : ℝ) = (parameter : ℝ) ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hlarge, Nat.cast_pow]
  have hq2 : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hlarge] using (Parameters.modulus_bounds parameter).2)
  have hratio : (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ≤ 2 * (parameter : ℝ) ^ 8 := by
    rw [hA]
    exact (div_le_iff₀ (by positivity)).mpr (by convert hq2 using 1; ring)
  have ha : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have hconst := activationConstant_pos cutoffScale hscale
  have hL1 : 192 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8) ≤
      (192 * activationConstant cutoffScale) / (parameter : ℝ) ^ (15 / 4 : ℝ) := by
    have heq : (parameter : ℝ) ^ (17 / 4 : ℝ) * (parameter : ℝ) ^ (15 / 4 : ℝ) = (parameter : ℝ) ^ 8 := by
      rw [← Real.rpow_add hx]
      norm_num
      exact Real.rpow_natCast _ 8
    calc
      _ = (192 / (parameter : ℝ) ^ 8) * (v7Activation cutoffScale parameter)⁻¹ := by ring
      _ ≤ (192 / (parameter : ℝ) ^ 8) * (activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (v7Activation_inverse_upper cutoffScale parameter hscale (by omega)) (by positivity)
      _ = _ := by rw [← heq]; field_simp
  have h8 : 1 ≤ (parameter : ℝ) ^ 8 := one_le_pow₀ hx1
  refine ⟨?_, ?_⟩
  · apply hs.2.2.trans
    have hprod : ((parameter : ℝ) ^ (15 / 4 : ℝ)) ^ 2 * (parameter : ℝ) ^ (1 / 2 : ℝ) = (parameter : ℝ) ^ 8 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
      norm_num
      exact Real.rpow_natCast _ 8
    calc
      _ ≤ 4 * (2 * (parameter : ℝ) ^ 8) * ((192 * activationConstant cutoffScale) / (parameter : ℝ) ^ (15 / 4 : ℝ)) ^ 2 + 16 := by
        have hratio' : 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ≤ 4 * (2 * (parameter : ℝ) ^ 8) := by
          convert mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4) using 1; ring
        have hsq := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hL1
        exact add_le_add (mul_le_mul hratio' hsq (by positivity) (by positivity)) le_rfl
      _ = (8 * (192 * activationConstant cutoffScale) ^ 2) * (parameter : ℝ) ^ (1 / 2 : ℝ) + 16 := by
        rw [← hprod]
        field_simp
        ring
      _ ≤ _ := by
        have hh := Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        unfold anchorSeedSquareConstant
        nlinarith
  · intro center
    have hb0 : 0 ≤ actualBodyCenter cutoffScale parameter (beta parameter) center :=
      (div_nonneg ((actualCoreLaw parameter).nonneg center) (by norm_num)).trans (hb.2.1 center).1
    by_cases hin : center ∈ safePalette parameter
    · let mean := blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (extraShift cutoffScale parameter) (extraBlur cutoffScale parameter)
        (actualPrimary cutoffScale parameter (beta parameter)) center.val
      have hm0 : 0 ≤ mean := Finset.sum_nonneg fun color _ => mul_nonneg (hp.1 color).le (blurredAnchorKernel_nonneg _ _ _ _ _ _)
      have hmUpper : mean ≤ (Parameters.anchorWidth parameter : ℝ)⁻¹ := by
        calc
          _ ≤ ∑ color, actualPrimary cutoffScale parameter (beta parameter) color * (Parameters.anchorWidth parameter : ℝ)⁻¹ :=
            Finset.sum_le_sum fun color _ => mul_le_mul_of_nonneg_left (blurredAnchorKernel_le _ _ _ _ _ _) (hp.1 color).le
          _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]
      have hcore := actualCoreLaw_bounds parameter
      have hpoint : |extraAnchorSeed cutoffScale parameter (beta parameter) center| ≤
          (Parameters.anchorWidth parameter : ℝ)⁻¹ + 2 / (Parameters.modulus parameter : ℝ) := by
        change |mean - (actualCoreLaw parameter).weight center| ≤ _
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg hm0, abs_of_nonneg ((actualCoreLaw parameter).nonneg center)]; exact add_le_add hmUpper (hcore.1 center))
      have hlower : (1 / (Parameters.modulus parameter : ℝ)) / 2 ≤ actualBodyCenter cutoffScale parameter (beta parameter) center :=
        (div_le_div_of_nonneg_right (hcore.2 center hin) (by norm_num)).trans (hb.2.1 center).1
      calc
        _ ≤ (Parameters.anchorWidth parameter : ℝ)⁻¹ + 2 / (Parameters.modulus parameter : ℝ) := hpoint
        _ = (2 * ((Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) + 4) *
            ((1 / (Parameters.modulus parameter : ℝ)) / 2) := by field_simp; ring
        _ ≤ (2 * ((Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) + 4) *
            actualBodyCenter cutoffScale parameter (beta parameter) center := mul_le_mul_of_nonneg_left hlower (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hb0
    · rw [hs.2.1 center hin, abs_zero]
      positivity

end V7Calibration
end
end AFT

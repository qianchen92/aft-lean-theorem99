import AFT.ReferenceProbability
import AFT.SafePairCore

/-! # The canonical safe seed of the actual marked endpoint pair -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem profileSquareNorm_sub_le_two (reference first second : ι → ℝ)
    (hr : ∀ i, 0 ≤ reference i) :
    profileSquareNorm reference (first - second) ≤ 2 * profileSquareNorm reference first + 2 * profileSquareNorm reference second := by
  unfold profileSquareNorm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change (first i - second i) ^ 2 / reference i ≤ _
  have hh : (first i - second i) ^ 2 ≤ 2 * first i ^ 2 + 2 * second i ^ 2 := by nlinarith [sq_nonneg (first i + second i)]
  exact (div_le_div_of_nonneg_right hh (hr i)).trans_eq (by ring)

theorem probability_difference_counting_sq (first second : ι → ℝ) (boundFirst boundSecond : ℝ)
    (hf : ∀ i, 0 ≤ first i) (hs : ∀ i, 0 ≤ second i)
    (hfm : ∑ i, first i = 1) (hsm : ∑ i, second i = 1)
    (hfb : ∀ i, first i ≤ boundFirst) (hsb : ∀ i, second i ≤ boundSecond) :
    (∑ i, (first i - second i) ^ 2) ≤ 2 * (boundFirst + boundSecond) := by
  calc
    _ ≤ ∑ i, (boundFirst + boundSecond) * (first i + second i) := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := mul_le_mul_of_nonneg_right (hfb i) (hf i)
      have h2 := mul_le_mul_of_nonneg_right (hsb i) (hs i)
      have hbf : 0 ≤ boundFirst := (hf i).trans (hfb i)
      have hbs : 0 ≤ boundSecond := (hs i).trans (hsb i)
      nlinarith [mul_nonneg (hf i) (hs i), mul_nonneg hbf (hs i), mul_nonneg hbs (hf i)]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, hfm, hsm]; ring

theorem profileSquareNorm_le_counting (reference profile : ι → ℝ) (safe : Finset ι) (lower : ℝ)
    (hl : 0 < lower) (hr : ∀ i ∈ safe, lower ≤ reference i)
    (hout : ∀ i ∉ safe, profile i = 0) :
    profileSquareNorm reference profile ≤ lower⁻¹ * ∑ i, profile i ^ 2 := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ safe
  · have hr0 := hl.trans_le (hr i hi)
    exact (div_le_div_of_nonneg_left (sq_nonneg _) hl (hr i hi)).trans_eq (by ring)
  · rw [hout i hi]
    simp

namespace V7Calibration
open GaussianSource

theorem actual_reference_le_primary_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color,
      actualReferenceMean cutoffScale parameter (beta parameter) color ≤ 8 * actualPrimary cutoffScale parameter (beta parameter) color := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta] with parameter hp hr color
  dsimp only at hp
  have hh := mul_le_mul_of_nonneg_left (hp.1 color) (by norm_num : (0 : ℝ) ≤ 8)
  exact (hr.1 color).2.trans (by convert hh using 1; ring)

def actualMarkedSafeSeed (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (color center : Fin (Parameters.modulus parameter)) : ℝ :=
  actualPrimary cutoffScale parameter beta color *
    (actualExtraAnchorKernel cutoffScale parameter color center.val - (actualCoreLaw parameter).weight center) -
      actualReferenceMean cutoffScale parameter beta color * extraAnchorSeed cutoffScale parameter beta center

def actualMarkedSafeDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (color center : Fin (Parameters.modulus parameter)) : ℝ :=
  actualMarkedSafeSeed cutoffScale parameter beta color center /
    (actualPrimary cutoffScale parameter beta color * actualBodyCenter cutoffScale parameter beta center)

theorem actual_marked_safe_canonical_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∀ color, ∑ center, actualMarkedSafeSeed cutoffScale parameter (beta parameter) color center = 0) ∧
      (∀ center, ∑ color, actualMarkedSafeSeed cutoffScale parameter (beta parameter) color center = 0) ∧
      (∀ color center, center ∉ safePalette parameter → actualMarkedSafeSeed cutoffScale parameter (beta parameter) color center = 0) := by
  filter_upwards [actual_extra_anchor_safe_eventually cutoffScale hscale,
    actual_extra_anchor_seed_bounds cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta]
    with parameter ha hs hp hr
  refine ⟨?_, ?_, ?_⟩
  · intro color
    simp only [actualMarkedSafeSeed, Finset.sum_sub_distrib, ← Finset.mul_sum, hs.1, (ha color).1,
      (actualCoreLaw parameter).sum_one, sub_self, mul_zero]
  · intro center
    simp only [actualMarkedSafeSeed, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, hr.2, one_mul,
      extraAnchorSeed, blurredAnchorMean, actualExtraAnchorKernel]
    ring
  · intro color center hout
    have hc : (actualCoreLaw parameter).weight center = 0 := by simp [actualCoreLaw, FiniteDist.uniformSafe, hout]
    have hh : (center.val : ℤ) < Parameters.safeMargin parameter ∨
        (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter ≤ center.val := by
      simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
        TrimmedSlice.mem_slice] at hout
      omega
    simp only [actualMarkedSafeSeed, (ha color).2 center.val hh, hc, hs.2.1 center hout, sub_self, mul_zero]

/-- Every individual true extra-blurred anchor has the full safe reference
L2 estimate, uniformly in its fixed primary color. -/
theorem actual_extra_anchor_row_bounds (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color,
      profileSquareNorm (actualBodyCenter cutoffScale parameter (beta parameter))
        (fun center => actualExtraAnchorKernel cutoffScale parameter color center.val - (actualCoreLaw parameter).weight center) ≤
        16 * (parameter : ℝ) ^ 8 ∧
      (∀ center, |actualExtraAnchorKernel cutoffScale parameter color center.val - (actualCoreLaw parameter).weight center| ≤
        (8 * (parameter : ℝ) ^ 8) * actualBodyCenter cutoffScale parameter (beta parameter) center) := by
  filter_upwards [actual_extra_anchor_safe_eventually cutoffScale hscale,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter ha hb hlarge color
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have h8 : 1 ≤ (parameter : ℝ) ^ 8 := one_le_pow₀ hx1
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hA : (Parameters.anchorWidth parameter : ℝ) = (parameter : ℝ) ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hlarge, Nat.cast_pow]
  have hq2 : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hlarge] using (Parameters.modulus_bounds parameter).2)
  have hratio : (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ≤ 2 * (parameter : ℝ) ^ 8 := by
    rw [hA]
    exact (div_le_iff₀ (by positivity)).mpr (by convert hq2 using 1; ring)
  let row : Fin (Parameters.modulus parameter) → ℝ := fun center => actualExtraAnchorKernel cutoffScale parameter color center.val
  let core := (actualCoreLaw parameter).weight
  let body := actualBodyCenter cutoffScale parameter (beta parameter)
  have hrow0 (center) : 0 ≤ row center := blurredAnchorKernel_nonneg _ _ _ _ _ _
  have hrowBound (center) : row center ≤ (Parameters.anchorWidth parameter : ℝ)⁻¹ := blurredAnchorKernel_le _ _ _ _ _ _
  have hcore := actualCoreLaw_bounds parameter
  have hout (center) (ho : center ∉ safePalette parameter) : row center - core center = 0 := by
    have hc : core center = 0 := by simp [core, actualCoreLaw, FiniteDist.uniformSafe, ho]
    have hh : (center.val : ℤ) < Parameters.safeMargin parameter ∨
        (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter ≤ center.val := by
      simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
        TrimmedSlice.mem_slice] at ho
      omega
    change actualExtraAnchorKernel cutoffScale parameter color center.val - core center = 0
    rw [(ha color).2 center.val hh, hc, sub_self]
  have hlower (center) (hin : center ∈ safePalette parameter) :
      (1 / (Parameters.modulus parameter : ℝ)) / 2 ≤ body center :=
    (div_le_div_of_nonneg_right (hcore.2 center hin) (by norm_num)).trans (hb.2.1 center).1
  have hc := probability_difference_counting_sq row core (Parameters.anchorWidth parameter : ℝ)⁻¹
    (2 / (Parameters.modulus parameter : ℝ)) hrow0 (actualCoreLaw parameter).nonneg (ha color).1 (actualCoreLaw parameter).sum_one
    hrowBound hcore.1
  refine ⟨?_, ?_⟩
  · have hh := profileSquareNorm_le_counting body (fun center => row center - core center) (safePalette parameter)
      ((1 / (Parameters.modulus parameter : ℝ)) / 2) (by positivity) hlower hout
    have ht := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ ((1 / (Parameters.modulus parameter : ℝ)) / 2)⁻¹)
    apply hh.trans (ht.trans ?_)
    have heq : ((1 / (Parameters.modulus parameter : ℝ)) / 2)⁻¹ *
        (2 * ((Parameters.anchorWidth parameter : ℝ)⁻¹ + 2 / (Parameters.modulus parameter : ℝ))) =
        4 * ((Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) + 8 := by field_simp; ring
    rw [heq]
    linarith
  · intro center
    have hb0 : 0 ≤ body center := (div_nonneg ((actualCoreLaw parameter).nonneg center) (by norm_num)).trans (hb.2.1 center).1
    by_cases hin : center ∈ safePalette parameter
    · have habs : |row center - core center| ≤ (Parameters.anchorWidth parameter : ℝ)⁻¹ + 2 / (Parameters.modulus parameter : ℝ) := by
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg (hrow0 center), abs_of_nonneg ((actualCoreLaw parameter).nonneg center)]; exact add_le_add (hrowBound center) (hcore.1 center))
      calc
        _ ≤ (Parameters.anchorWidth parameter : ℝ)⁻¹ + 2 / (Parameters.modulus parameter : ℝ) := habs
        _ = (2 * ((Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) + 4) *
            ((1 / (Parameters.modulus parameter : ℝ)) / 2) := by field_simp; ring
        _ ≤ (2 * ((Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) + 4) * body center :=
          mul_le_mul_of_nonneg_left (hlower center hin) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hb0
    · change |row center - core center| ≤ _
      rw [hout center hin, abs_zero]
      positivity

def markedPairSquareConstant (cutoffScale : ℝ) : ℝ := 32 + 128 * anchorSeedSquareConstant cutoffScale

/-- Every mixed fiber of the actual marked safe kernel is retained:
full L2, fixed primary, fixed body, and full pointwise density. -/
theorem actual_marked_safe_all_fibers (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∀ color, (∑ center, actualBodyCenter cutoffScale parameter (beta parameter) center *
        actualMarkedSafeDensity cutoffScale parameter (beta parameter) color center ^ 2) ≤
          markedPairSquareConstant cutoffScale * (parameter : ℝ) ^ 8) ∧
      (∀ color center, |actualMarkedSafeDensity cutoffScale parameter (beta parameter) color center| ≤ 72 * (parameter : ℝ) ^ 8) ∧
      (∑ color, ∑ center, actualPrimary cutoffScale parameter (beta parameter) color *
        actualBodyCenter cutoffScale parameter (beta parameter) center *
          actualMarkedSafeDensity cutoffScale parameter (beta parameter) color center ^ 2) ≤
        markedPairSquareConstant cutoffScale * (parameter : ℝ) ^ 8 ∧
      (∀ center, (∑ color, actualPrimary cutoffScale parameter (beta parameter) color *
        actualMarkedSafeDensity cutoffScale parameter (beta parameter) color center ^ 2) ≤
          (72 * (parameter : ℝ) ^ 8) ^ 2) := by
  filter_upwards [actual_extra_anchor_row_bounds cutoffScale hscale beta hbeta,
    actual_extra_anchor_seed_power_bounds cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_le_primary_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hrow hseed hbody hp hr hcompare hlarge
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  let body := actualBodyCenter cutoffScale parameter (beta parameter)
  let seed := extraAnchorSeed cutoffScale parameter (beta parameter)
  let density := actualMarkedSafeDensity cutoffScale parameter (beta parameter)
  let row : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ :=
    fun color center => actualExtraAnchorKernel cutoffScale parameter color center.val - (actualCoreLaw parameter).weight center
  have hb0 (center) : 0 ≤ body center :=
    (div_nonneg ((actualCoreLaw parameter).nonneg center) (by norm_num)).trans (hbody.2.1 center).1
  have hratio (color) : 0 ≤ r color / p color ∧ r color / p color ≤ 8 := by
    exact ⟨div_nonneg (hr.1 color).1 (hp.1 color).le, (div_le_iff₀ (hp.1 color)).mpr (hcompare color)⟩
  have hdensity (color center) : density color center =
      (row color center - (r color / p color) * seed center) / body center := by
    dsimp only [density, actualMarkedSafeDensity, actualMarkedSafeSeed, p, r, row, seed, body]
    field_simp [ne_of_gt (hp.1 color)]
  have hrowEq (color) : (∑ center, body center * density color center ^ 2) =
      profileSquareNorm body (row color - (r color / p color) • seed) := by
    simp_rw [hdensity]
    exact densityScore_square body (row color - (r color / p color) • seed)
  have hconst : 0 ≤ anchorSeedSquareConstant cutoffScale := by unfold anchorSeedSquareConstant; positivity
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hpower : (parameter : ℝ) ^ (1 / 2 : ℝ) ≤ (parameter : ℝ) ^ 8 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ (8 : ℕ))
  have hfixed (color) : (∑ center, body center * density color center ^ 2) ≤
      markedPairSquareConstant cutoffScale * (parameter : ℝ) ^ 8 := by
    rw [hrowEq]
    have hh := profileSquareNorm_sub_le_two body (row color) ((r color / p color) • seed) hb0
    rw [profileSquareNorm_smul] at hh
    have hs0 := profileSquareNorm_nonneg body seed hb0
    have hrsq : (r color / p color) ^ 2 ≤ 64 := by nlinarith [(hratio color).1, (hratio color).2]
    have hhseed : (r color / p color) ^ 2 * profileSquareNorm body seed ≤
        64 * (anchorSeedSquareConstant cutoffScale * (parameter : ℝ) ^ 8) := by
      exact mul_le_mul hrsq (hseed.1.trans (mul_le_mul_of_nonneg_left hpower hconst)) hs0 (by norm_num)
    calc
      _ ≤ 2 * profileSquareNorm body (row color) + 2 * ((r color / p color) ^ 2 * profileSquareNorm body seed) := hh
      _ ≤ 2 * (16 * (parameter : ℝ) ^ 8) + 2 * (64 * (anchorSeedSquareConstant cutoffScale * (parameter : ℝ) ^ 8)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hrow color).1 (by norm_num)) (mul_le_mul_of_nonneg_left hhseed (by norm_num))
      _ = _ := by unfold markedPairSquareConstant; ring
  have hpoint (color center) : |density color center| ≤ 72 * (parameter : ℝ) ^ 8 := by
    have hprofile : |row color center - (r color / p color) * seed center| ≤
        (72 * (parameter : ℝ) ^ 8) * body center := by
      calc
        _ ≤ |row color center| + |(r color / p color) * seed center| := abs_sub _ _
        _ = |row color center| + (r color / p color) * |seed center| := by rw [abs_mul, abs_of_nonneg (hratio color).1]
        _ ≤ (8 * (parameter : ℝ) ^ 8) * body center + 8 * ((8 * (parameter : ℝ) ^ 8) * body center) :=
          add_le_add ((hrow color).2 center) (mul_le_mul (hratio color).2 (hseed.2 center) (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    rw [hdensity, abs_div, abs_of_nonneg (hb0 center)]
    by_cases hb : body center = 0
    · simp [hb]
    · exact (div_le_iff₀ (lt_of_le_of_ne (hb0 center) (Ne.symm hb))).mpr hprofile
  refine ⟨hfixed, hpoint, ?_, ?_⟩
  · calc
      _ = ∑ color, p color * ∑ center, body center * density color center ^ 2 := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        apply Finset.sum_congr rfl
        intro center _
        ring
      _ ≤ ∑ color, p color * (markedPairSquareConstant cutoffScale * (parameter : ℝ) ^ 8) :=
        Finset.sum_le_sum fun color _ => mul_le_mul_of_nonneg_left (hfixed color) (hp.1 color).le
      _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]
  · intro center
    calc
      _ ≤ ∑ color, p color * (72 * (parameter : ℝ) ^ 8) ^ 2 := by
        apply Finset.sum_le_sum
        intro color _
        have hh := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.mpr (hpoint color center)
        rw [sq_abs] at hh
        exact mul_le_mul_of_nonneg_left hh (hp.1 color).le
      _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]

end V7Calibration
end
end AFT

import AFT.AnchorMean
import AFT.V7SafeProjection

/-! # Safe public anchor kernels with the actual optional blur -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem intervalAnchorLaw_palette_mass (modulus width : ℕ) (start : ℤ) (hw : width ≠ 0)
    (hsupport : ∀ output ∈ anchorInterval start width, 0 ≤ output ∧ output < modulus) :
    (∑ color : Fin modulus, intervalAnchorLaw start width color.val) = 1 := by
  let support : Finset (Fin modulus) := Finset.univ.filter fun c => (c.val : ℤ) ∈ anchorInterval start width
  have hc : support.card = width := by
    have hh := Finset.card_bij (s := support) (t := anchorInterval start width)
      (fun (c : Fin modulus) _ => (c.val : ℤ))
      (by intro c hc; exact (Finset.mem_filter.mp hc).2)
      (by intro a _ b _ h; change (a.val : ℤ) = b.val at h; apply Fin.ext; exact_mod_cast h)
      (by
        intro output hout
        have hb := hsupport output hout
        let point : Fin modulus := ⟨output.toNat, by omega⟩
        have heq : (point.val : ℤ) = output := by dsimp [point]; omega
        exact ⟨point, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [heq] using hout⟩, heq⟩)
    simpa only [anchorInterval_card] using hh
  simp only [intervalAnchorLaw, ← Finset.sum_filter]
  change (∑ _color ∈ support, (width : ℝ)⁻¹) = 1
  simp [hc, Nat.cast_ne_zero.mpr hw]

namespace V7Calibration
open GaussianSource

def blurredAnchorKernel {σ : Type*} [Fintype σ] (modulus width : ℕ)
    (shifts : σ → ℤ) (distribution : FiniteDist σ) (color : Fin modulus) (output : ℤ) : ℝ :=
  ∑ sample, distribution.weight sample * publicAnchorKernel modulus width color (output - shifts sample)

def blurredAnchorMean {σ : Type*} [Fintype σ] (modulus width : ℕ)
    (shifts : σ → ℤ) (distribution : FiniteDist σ) (profile : Fin modulus → ℝ) (output : ℤ) : ℝ :=
  ∑ color, profile color * blurredAnchorKernel modulus width shifts distribution color output

theorem blurredAnchorKernel_nonneg {σ : Type*} [Fintype σ] (modulus width : ℕ)
    (shifts : σ → ℤ) (distribution : FiniteDist σ) (color : Fin modulus) (output : ℤ) :
    0 ≤ blurredAnchorKernel modulus width shifts distribution color output := by
  exact Finset.sum_nonneg fun sample _ => mul_nonneg (distribution.nonneg sample) (publicAnchorKernel_nonneg _ _ _ _)

theorem blurredAnchorKernel_le {σ : Type*} [Fintype σ] (modulus width : ℕ)
    (shifts : σ → ℤ) (distribution : FiniteDist σ) (color : Fin modulus) (output : ℤ) :
    blurredAnchorKernel modulus width shifts distribution color output ≤ (width : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ sample, distribution.weight sample * (width : ℝ)⁻¹ :=
      Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (publicAnchorKernel_le _ _ _ _) (distribution.nonneg sample)
    _ = _ := by rw [← Finset.sum_mul, distribution.sum_one, one_mul]

theorem blurredAnchorKernel_column_bound {σ : Type*} [Fintype σ] (modulus width : ℕ)
    (shifts : σ → ℤ) (distribution : FiniteDist σ) (output : ℤ) :
    (∑ color, blurredAnchorKernel modulus width shifts distribution color output) ≤ 2 := by
  unfold blurredAnchorKernel
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  calc
    _ ≤ ∑ sample, distribution.weight sample * 2 :=
      Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (publicAnchorKernel_column_bound _ _ _) (distribution.nonneg sample)
    _ = 2 := by rw [← Finset.sum_mul, distribution.sum_one, one_mul]

theorem publicAnchorKernel_translate (modulus width : ℕ) (color : Fin modulus) (output shift : ℤ) :
    publicAnchorKernel modulus width color (output - shift) =
      (intervalAnchorLaw (publicAnchorStart modulus width color true + shift) width output +
        intervalAnchorLaw (publicAnchorStart modulus width color false + shift) width output) / 2 := by
  simp only [publicAnchorKernel, intervalAnchorLaw_translate]

theorem publicAnchorKernel_safe_mass (modulus width : ℕ) (margin shift : ℤ)
    (hw : width ≠ 0) (hmodulus : 6 * width + 1 ≤ modulus) (hm0 : 0 ≤ margin)
    (hmargin : margin + |shift| ≤ width) (color : Fin modulus) :
    (∑ output : Fin modulus, publicAnchorKernel modulus width color ((output.val : ℤ) - shift)) = 1 ∧
    (∀ output : ℤ, output < margin ∨ (modulus : ℤ) - margin ≤ output →
      publicAnchorKernel modulus width color (output - shift) = 0) := by
  have hs (coin : Bool) (output : ℤ)
      (hout : output ∈ anchorInterval (publicAnchorStart modulus width color coin + shift) width) :=
    publicAnchorStart_safe modulus width color coin shift margin hmodulus hmargin output hout
  constructor
  · simp only [publicAnchorKernel_translate, ← Finset.sum_div, Finset.sum_add_distrib]
    rw [intervalAnchorLaw_palette_mass modulus width _ hw (by intro output hout; have hh := hs true output hout; omega),
      intervalAnchorLaw_palette_mass modulus width _ hw (by intro output hout; have hh := hs false output hout; omega)]
    norm_num
  · intro output hout
    have hz (coin : Bool) : intervalAnchorLaw (publicAnchorStart modulus width color coin + shift) width output = 0 := by
      unfold intervalAnchorLaw
      split_ifs with hmem
      · have hh := hs coin output hmem; omega
      · rfl
    rw [publicAnchorKernel_translate, hz true, hz false]
    norm_num

theorem blurredAnchorKernel_safe_mass {σ : Type*} [Fintype σ] (modulus width : ℕ) (margin : ℤ)
    (shifts : σ → ℤ) (distribution : FiniteDist σ)
    (hw : width ≠ 0) (hmodulus : 6 * width + 1 ≤ modulus) (hm0 : 0 ≤ margin)
    (hmargin : ∀ sample, margin + |shifts sample| ≤ width) (color : Fin modulus) :
    (∑ output : Fin modulus, blurredAnchorKernel modulus width shifts distribution color output.val) = 1 ∧
    (∀ output : ℤ, output < margin ∨ (modulus : ℤ) - margin ≤ output →
      blurredAnchorKernel modulus width shifts distribution color output = 0) := by
  constructor
  · unfold blurredAnchorKernel
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (publicAnchorKernel_safe_mass modulus width margin _ hw hmodulus hm0 (hmargin _) color).1,
      mul_one]
    exact distribution.sum_one
  · intro output hout
    unfold blurredAnchorKernel
    simp_rw [(publicAnchorKernel_safe_mass modulus width margin _ hw hmodulus hm0 (hmargin _) color).2 output hout,
      mul_zero, Finset.sum_const_zero]

def actualExtraAnchorKernel (cutoffScale : ℝ) (parameter : ℕ) : Fin (Parameters.modulus parameter) → ℤ → ℝ :=
  blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (extraShift cutoffScale parameter) (extraBlur cutoffScale parameter)

theorem extraShift_abs_le (cutoffScale : ℝ) (parameter : ℕ) (sample : extraSample cutoffScale parameter) :
    |extraShift cutoffScale parameter sample| ≤ (maxBodyShift cutoffScale parameter : ℤ) := by
  have hh := (abs_add_le (optionalShift sample.1) (optionalShift sample.2)).trans
    (add_le_add (optionalShift_abs_le sample.1) (optionalShift_abs_le sample.2))
  unfold extraShift maxBodyShift
  push_cast
  exact hh.trans (by omega)

/-- Every extra-blurred anchor remains in the actual safe-center interval,
and its full palette mass is exactly one. -/
theorem actual_extra_anchor_safe_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ color : Fin (Parameters.modulus parameter),
      (∑ output : Fin (Parameters.modulus parameter), actualExtraAnchorKernel cutoffScale parameter color output.val) = 1 ∧
      (∀ output : ℤ, output < (Parameters.safeMargin parameter : ℤ) ∨
        (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter ≤ output →
        actualExtraAnchorKernel cutoffScale parameter color output = 0) := by
  filter_upwards [legCutoff_le_square_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hcut hp color
  have hm : Parameters.safeMargin parameter + maxBodyShift cutoffScale parameter ≤ Parameters.anchorWidth parameter := by
    have h25 : 25 ≤ parameter ^ 30 := by have hh := Nat.pow_le_pow_left hp 30; omega
    have hh := Nat.mul_le_mul_right (parameter ^ 2) h25
    have hA : 25 * parameter ^ 2 ≤ Parameters.anchorWidth parameter := by
      simpa only [Parameters.anchorWidth, Parameters.security_eq parameter hp, ← pow_add] using hh
    simp only [Parameters.safeMargin, Parameters.security_eq parameter hp, maxBodyShift, v7RootCutoff, queueCutoff] at *
    omega
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp]
    positivity
  apply blurredAnchorKernel_safe_mass _ _ _ _ _ hw (Parameters.anchor_clearance parameter) (by positivity)
  intro sample
  have hh := extraShift_abs_le cutoffScale parameter sample
  have hm' : (Parameters.safeMargin parameter : ℤ) + maxBodyShift cutoffScale parameter ≤ Parameters.anchorWidth parameter := by exact_mod_cast hm
  linarith

end V7Calibration
end
end AFT

import AFT.ActualTriples

/-! # Exact output of the real marked safe seed under the root marginal -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem integerShiftProfile_function (parameter : ℕ) (profile : ℤ → ℝ)
    (houtside : ∀ z, z < 0 ∨ (Parameters.modulus parameter : ℤ) ≤ z → profile z = 0)
    (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    integerShiftProfile parameter (fun center => profile center.val) shift output = profile ((output.val : ℤ) - shift) := by
  let target := (output.val : ℤ) - shift
  by_cases htarget : 0 ≤ target ∧ target < Parameters.modulus parameter
  · let center : Fin (Parameters.modulus parameter) := ⟨target.toNat, by omega⟩
    have heq : (center.val : ℤ) = target := by dsimp [center]; omega
    have hmatch (point : Fin (Parameters.modulus parameter)) : ((output.val : ℤ) = (point.val : ℤ) + shift) ↔ point = center := by
      constructor
      · intro hh
        apply Fin.ext
        have hh' : (point.val : ℤ) = center.val := by dsimp [target] at heq; omega
        exact_mod_cast hh'
      · rintro rfl
        dsimp [target] at heq
        omega
    unfold integerShiftProfile
    simp only [hmatch, Finset.sum_ite_eq', Finset.mem_univ, if_true, heq]
    rfl
  · have hz : profile target = 0 := houtside target (by omega)
    change _ = profile target
    rw [hz]
    unfold integerShiftProfile
    apply Finset.sum_eq_zero
    intro point _
    have hn : ¬ ((output.val : ℤ) = (point.val : ℤ) + shift) := by
      have hp := point.isLt
      dsimp [target] at htarget
      omega
    simp only [if_neg hn]

def rootProfileOperator (parameter : ℕ) : Module.End ℝ (Fin (Parameters.modulus parameter) → ℝ) where
  toFun profile output := ∑ root : Window (v7RootCutoff parameter),
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter)).weight root * integerShiftProfile parameter profile root output
  map_add' first second := by
    funext output
    simp only [integerShiftProfile, Pi.add_apply]
    have hpoint (root : Window (v7RootCutoff parameter)) (center : Fin (Parameters.modulus parameter)) :
        (if (output.val : ℤ) = (center.val : ℤ) + root then first center + second center else 0) =
        (if (output.val : ℤ) = (center.val : ℤ) + root then first center else 0) +
        (if (output.val : ℤ) = (center.val : ℤ) + root then second center else 0) := by split_ifs <;> ring
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, mul_add]
  map_smul' scalar profile := by
    funext output
    simp only [integerShiftProfile, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hpoint (root : Window (v7RootCutoff parameter)) (center : Fin (Parameters.modulus parameter)) :
        (if (output.val : ℤ) = (center.val : ℤ) + root then scalar * profile center else 0) =
        scalar * (if (output.val : ℤ) = (center.val : ℤ) + root then profile center else 0) := by split_ifs <;> ring
    simp_rw [hpoint]
    simp only [← Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro root _
    ring

theorem rootProfileOperator_function (parameter : ℕ) (profile : ℤ → ℝ)
    (houtside : ∀ z, z < 0 ∨ (Parameters.modulus parameter : ℤ) ≤ z → profile z = 0)
    (output : Fin (Parameters.modulus parameter)) :
    rootProfileOperator parameter (fun center => profile center.val) output =
      ∑ root : Window (v7RootCutoff parameter),
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)).weight root * profile ((output.val : ℤ) - root) := by
  change (∑ root : Window (v7RootCutoff parameter), _ * integerShiftProfile parameter _ root output) = _
  simp_rw [integerShiftProfile_function parameter profile houtside]

def coreIntegerProfile (parameter : ℕ) : ℤ → ℝ :=
  intervalAnchorLaw (Parameters.safeMargin parameter) (Parameters.safeSize parameter)

theorem coreIntegerProfile_safeSize (parameter : ℕ) :
    ((Parameters.modulus parameter : ℤ) - 2 * Parameters.safeMargin parameter).toNat = Parameters.safeSize parameter := by
  unfold Parameters.safeSize
  omega

theorem coreIntegerProfile_on_palette (parameter : ℕ) (center : Fin (Parameters.modulus parameter)) :
    coreIntegerProfile parameter center.val = (actualCoreLaw parameter).weight center := by
  have hsize := Parameters.safeSize_positive parameter
  have hh : (Parameters.safeMargin parameter : ℤ) + Parameters.safeSize parameter =
      (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter := by
    unfold Parameters.safeSize at *
    omega
  have hmem : (center.val : ℤ) ∈ anchorInterval (Parameters.safeMargin parameter) (Parameters.safeSize parameter) ↔
      center ∈ safePalette parameter := by
    simp only [anchorInterval, Finset.mem_Ico, hh, safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter,
      Finset.mem_univ, true_and, TrimmedSlice.mem_slice]
    omega
  rw [actualCoreLaw_weight]
  unfold coreIntegerProfile intervalAnchorLaw uniformFiniteProfile
  simp only [hmem, safePalette_card]

theorem coreIntegerProfile_support (parameter : ℕ) (output : ℤ)
    (hout : output < 0 ∨ (Parameters.modulus parameter : ℤ) ≤ output) : coreIntegerProfile parameter output = 0 := by
  have hsize := Parameters.safeSize_positive parameter
  have hh : (Parameters.safeMargin parameter : ℤ) + Parameters.safeSize parameter =
      (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter := by
    unfold Parameters.safeSize at *
    omega
  have hn : output ∉ anchorInterval (Parameters.safeMargin parameter) (Parameters.safeSize parameter) := by
    simp only [anchorInterval, Finset.mem_Ico, hh]
    omega
  simp only [coreIntegerProfile, intervalAnchorLaw, if_neg hn]

/-- The actual root-only body mean is the exact root image of the core. -/
theorem rootProfileOperator_core (parameter : ℕ) :
    rootProfileOperator parameter (actualCoreLaw parameter).weight = actualRootBodyMean parameter := by
  funext output
  have heq : (actualCoreLaw parameter).weight = fun center => coreIntegerProfile parameter center.val :=
    funext fun center => (coreIntegerProfile_on_palette parameter center).symm
  rw [heq, rootProfileOperator_function parameter _ (coreIntegerProfile_support parameter)]
  simp only [actualRootBodyMean, bodyMean, TrimmedSlice.blurredSafeLaw, coreIntegerProfile, coreIntegerProfile_safeSize]

/-- Factoring the literal public body blur into root and optional shifts
is an exact finite-sum identity. -/
theorem fullAnchor_root_extra (cutoffScale : ℝ) (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) (output : ℤ) :
    blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) color output =
    ∑ root : Window (v7RootCutoff parameter),
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)).weight root * actualExtraAnchorKernel cutoffScale parameter color (output - root) := by
  simp only [blurredAnchorKernel, bodyBlur, bodyShift, FiniteDist.prod_weight, bodySample, Fintype.sum_prod_type,
    actualExtraAnchorKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root _
  apply Finset.sum_congr rfl
  intro extra _
  have heq : output - ((root : ℤ) + extraShift cutoffScale parameter extra) =
      (output - root) - extraShift cutoffScale parameter extra := by ring
  rw [heq]
  ring

/-- The safe finite input is evaluated by the actual integer root operator,
with no circular wrap or Gaussian approximation. -/
theorem actual_extra_anchor_root_image_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ color : Fin (Parameters.modulus parameter),
      rootProfileOperator parameter (fun center => actualExtraAnchorKernel cutoffScale parameter color center.val) =
        fun output => blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
          (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) color output.val := by
  filter_upwards [actual_extra_anchor_safe_eventually cutoffScale hscale] with parameter hs color
  funext output
  have hout (z : ℤ) (hz : z < 0 ∨ (Parameters.modulus parameter : ℤ) ≤ z) :
      actualExtraAnchorKernel cutoffScale parameter color z = 0 := by
    apply (hs color).2 z
    omega
  rw [rootProfileOperator_function parameter _ hout, fullAnchor_root_extra]

theorem actual_full_anchor_safe_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ color : Fin (Parameters.modulus parameter),
      (∑ output : Fin (Parameters.modulus parameter), blurredAnchorKernel (Parameters.modulus parameter)
        (Parameters.anchorWidth parameter) (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) color output.val) = 1 ∧
      (∀ output : ℤ, output < (Parameters.safeMargin parameter : ℤ) ∨
        (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter ≤ output →
        blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
          (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) color output = 0) := by
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
  have hh := bodyShift_abs_le cutoffScale parameter sample
  have hm' : (Parameters.safeMargin parameter : ℤ) + maxBodyShift cutoffScale parameter ≤ Parameters.anchorWidth parameter := by exact_mod_cast hm
  linarith

/-- The exact root output of the averaged safe anchor seed. -/
theorem actual_extra_seed_root_image_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ beta : ℝ,
      rootProfileOperator parameter (extraAnchorSeed cutoffScale parameter beta) =
        fun output => (∑ color, actualMarkedPair cutoffScale parameter beta color output) - actualRootBodyMean parameter output := by
  filter_upwards [actual_extra_anchor_root_image_eventually cutoffScale hscale] with parameter hs beta
  have heq : extraAnchorSeed cutoffScale parameter beta =
      (∑ color, actualPrimary cutoffScale parameter beta color •
        (fun center : Fin (Parameters.modulus parameter) => actualExtraAnchorKernel cutoffScale parameter color center.val)) -
          (actualCoreLaw parameter).weight := by
    funext center
    simp only [extraAnchorSeed, blurredAnchorMean, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, actualExtraAnchorKernel]
  rw [heq, map_sub, map_sum, rootProfileOperator_core]
  simp_rw [map_smul, hs]
  funext output
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, actualMarkedPair]

/-- The marked pair has the precise safe-body image plus the small
all-primary fringe required by the background certificate. -/
theorem actual_marked_canonical_root_decomposition (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ first second,
      SafePair.canonicalPair (actualReferenceMean cutoffScale parameter (beta parameter))
        (actualMarkedPair cutoffScale parameter (beta parameter)) first second =
      rootProfileOperator parameter (actualMarkedSafeSeed cutoffScale parameter (beta parameter) first) second +
        (actualPrimary cutoffScale parameter (beta parameter) first - actualReferenceMean cutoffScale parameter (beta parameter) first) *
          (actualRootBodyMean parameter second - actualReferenceMean cutoffScale parameter (beta parameter) second) := by
  filter_upwards [actual_extra_anchor_root_image_eventually cutoffScale hscale,
    actual_extra_seed_root_image_eventually cutoffScale hscale,
    actual_full_anchor_safe_eventually cutoffScale hscale,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta]
    with parameter hrow hseed hsafe hp first second
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  let companion : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ :=
    fun color output => blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) color output.val
  have hmarginal (color) : (∑ output, actualMarkedPair cutoffScale parameter (beta parameter) color output) = p color := by
    simp only [actualMarkedPair, ← Finset.mul_sum, (hsafe color).1, mul_one]
    rfl
  have hp' : (∑ color, p color) = 1 := hp.2
  have hK : actualMarkedSafeSeed cutoffScale parameter (beta parameter) first =
      p first • ((fun center : Fin (Parameters.modulus parameter) => actualExtraAnchorKernel cutoffScale parameter first center.val) -
        (actualCoreLaw parameter).weight) - r first • extraAnchorSeed cutoffScale parameter (beta parameter) := by
    funext center
    rfl
  rw [hK, map_sub, map_smul, map_smul, map_sub, hrow first, rootProfileOperator_core, hseed]
  simp only [SafePair.canonicalPair, hmarginal, hp', one_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change p first * companion first second - r first * (∑ color, actualMarkedPair cutoffScale parameter (beta parameter) color second) -
      p first * r second + r first * r second = _
  ring

end
end AFT.V7Calibration

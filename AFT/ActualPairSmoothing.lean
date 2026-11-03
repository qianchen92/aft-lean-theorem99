import AFT.IntegerPaletteTranslation
import AFT.CoreWindowKernel
import AFT.SmoothingDifference

/-! # Actual compact-box approximation to the core-restricted integer pair -/

namespace AFT.GaussianSource

open scoped BigOperators Classical
open AFT.SafeConvolution

noncomputable section

attribute [local instance] actualModulusNeZero

/-- The complete smoothing error of the original integer-window pair,
restricted to a reserved core. Window edges, the true reciprocal
slice denominator, endpoint masks, and no-wrap are all included. -/
theorem restrictedPair_box_square_le (parameter coreDepth radius : ℕ)
    (boundary start source shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ Parameters.modulus parameter) (hboundary : boundary ≤ coreDepth)
    (hradius : radius ≤ coreDepth)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound) (hsource : |source| ≤ cutoff)
    (hclear : lower ≤ (Parameters.modulus parameter : ℝ) - 2 * boundary - shiftBound - cutoff) :
    let mass : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ :=
      fun color => SafePair.restrictPair (TrimmedSlice.paletteSlice (Parameters.modulus parameter) coreDepth 0)
        (TrimmedSlice.averagedPair (Parameters.modulus parameter) boundary start source width) color.1 color.2
    let smooth := boxDistribution (paletteEmbedding parameter) (-(radius : ℤ)) (2 * radius + 1) (by omega)
    (∑ color, (convolution smooth.weight mass color - mass color) ^ 2) ≤
      16 * (Parameters.modulus parameter : ℝ) * radius / (lower ^ 2 * (width : ℝ) ^ 2) +
      16 * (Parameters.modulus parameter : ℝ) * (radius : ℝ) ^ 2 / (lower ^ 4 * width) +
      8 * (radius : ℝ) / (lower ^ 2 * width) := by
  let integerMass := TrimmedSlice.maskedIntegerPair (Parameters.modulus parameter) boundary lower start source width
    coreDepth (Parameters.modulus parameter - 2 * coreDepth)
  let profile : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ :=
    fun color => integerMass color.1.val color.2.val
  have heq (color : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter)) :
      SafePair.restrictPair (TrimmedSlice.paletteSlice (Parameters.modulus parameter) coreDepth 0)
        (TrimmedSlice.averagedPair (Parameters.modulus parameter) boundary start source width) color.1 color.2 = profile color :=
    TrimmedSlice.restricted_averagedPair_eq_maskedIntegerPair _ _ _ _ _ _ _ _ _ hlower hcore hboundary hstarts hsource hclear _ _
  dsimp only
  simp only [heq]
  apply convolution_difference_square_le_uniform
  intro shift hshift
  obtain ⟨u, v, hu, hu', hv, hv', hshiftEq⟩ := box_supportBox (paletteEmbedding parameter) radius shift hshift
  have habu : |u| ≤ (radius : ℤ) := abs_le.mpr ⟨hu, hu'⟩
  have habv : |v| ≤ (radius : ℤ) := abs_le.mpr ⟨hv, hv'⟩
  have hsupport (first second : ℤ) (hn : integerMass first second ≠ 0) :
      ((coreDepth : ℤ) ≤ first ∧ first < (Parameters.modulus parameter : ℤ) - coreDepth) ∧
      ((coreDepth : ℤ) ≤ second ∧ second < (Parameters.modulus parameter : ℤ) - coreDepth) := by
    dsimp [integerMass, TrimmedSlice.maskedIntegerPair] at hn
    split_ifs at hn with hmask
    · exact ⟨(TrimmedSlice.core_interval_mem _ _ hcore _).mp hmask.1,
        (TrimmedSlice.core_interval_mem _ _ hcore _).mp hmask.2⟩
    · exact (hn rfl).elim
  have htranslation (color : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter)) :
      profile (color - shift) = integerMass ((color.1.val : ℤ) - u) ((color.2.val : ℤ) - v) := by
    rw [hshiftEq]
    exact core_profile_translation_eq parameter coreDepth (by positivity) integerMass hsupport u v
      (habu.trans (by exact_mod_cast hradius)) (habv.trans (by exact_mod_cast hradius)) color.1 color.2
  simp only [htranslation]
  rw [Fintype.sum_prod_type]
  have hinj : Function.Injective (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ)) := by
    intro a b hab
    apply Fin.ext
    dsimp only at hab
    exact_mod_cast hab
  have hh := TrimmedSlice.maskedIntegerPair_translation_square_le
    (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ)) hinj (Parameters.modulus parameter)
    boundary lower hlower start source u v coreDepth width (Parameters.modulus parameter - 2 * coreDepth)
  simp only [Fintype.card_fin] at hh
  have habuR : |(u : ℝ)| ≤ radius := by exact_mod_cast habu
  have habvR : |(v : ℝ)| ≤ radius := by exact_mod_cast habv
  have habsum : |((u + v : ℤ) : ℝ)| ≤ 2 * (radius : ℝ) := by
    push_cast
    linarith [abs_add_le (u : ℝ) v]
  have hsum : ((u + v).natAbs : ℝ) ≤ 2 * radius := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using habsum
  have hsquare : (((u + v : ℤ) : ℝ)) ^ 2 ≤ (2 * (radius : ℝ)) ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg _) habsum
  have hboth : (u.natAbs : ℝ) + v.natAbs ≤ 2 * radius := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, two_mul] using add_le_add habuR habvR
  apply hh.trans
  calc
    _ ≤ 2 * (Parameters.modulus parameter : ℝ) *
        (4 * (2 * (radius : ℝ)) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * (2 * (radius : ℝ)) ^ 2 / (lower ^ 4 * width)) +
        4 * (2 * (radius : ℝ)) / (lower ^ 2 * width) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) (by positivity)
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by norm_num)) (by positivity)
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hboth (by norm_num)) (by positivity)
    _ = _ := by ring

/-- The same complete estimate holds for the actual sign/source mixture;
all mixing is performed before the Hilbert bound. -/
theorem restrictedMixedPair_box_square_le {σ : Type*} [Fintype σ]
    (parameter coreDepth radius : ℕ) (boundary shiftBound cutoff : ℤ)
    (starts sources : σ → ℤ) (sourceLaw : FiniteDist σ)
    (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ Parameters.modulus parameter) (hboundary : boundary ≤ coreDepth)
    (hradius : radius ≤ coreDepth)
    (hstarts : ∀ sample shift, shift ∈ anchorInterval (starts sample) width → |shift| ≤ shiftBound)
    (hsources : ∀ sample, |sources sample| ≤ cutoff)
    (hclear : lower ≤ (Parameters.modulus parameter : ℝ) - 2 * boundary - shiftBound - cutoff) :
    let mass : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ :=
      fun color => SafePair.restrictPair (TrimmedSlice.paletteSlice (Parameters.modulus parameter) coreDepth 0)
        (TrimmedSlice.mixedPair (Parameters.modulus parameter) boundary starts sources sourceLaw.weight width) color.1 color.2
    let smooth := boxDistribution (paletteEmbedding parameter) (-(radius : ℤ)) (2 * radius + 1) (by omega)
    (∑ color, (convolution smooth.weight mass color - mass color) ^ 2) ≤
      16 * (Parameters.modulus parameter : ℝ) * radius / (lower ^ 2 * (width : ℝ) ^ 2) +
      16 * (Parameters.modulus parameter : ℝ) * (radius : ℝ) ^ 2 / (lower ^ 4 * width) +
      8 * (radius : ℝ) / (lower ^ 2 * width) := by
  let component (sample : σ) (color : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter)) :=
    SafePair.restrictPair (TrimmedSlice.paletteSlice (Parameters.modulus parameter) coreDepth 0)
      (TrimmedSlice.averagedPair (Parameters.modulus parameter) boundary (starts sample) (sources sample) width) color.1 color.2
  have hmass : (fun color : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) =>
      SafePair.restrictPair (TrimmedSlice.paletteSlice (Parameters.modulus parameter) coreDepth 0)
        (TrimmedSlice.mixedPair (Parameters.modulus parameter) boundary starts sources sourceLaw.weight width) color.1 color.2) =
      (fun color => ∑ sample, sourceLaw.weight sample * component sample color) := by
    funext color
    by_cases hc : color.1 ∈ TrimmedSlice.paletteSlice (Parameters.modulus parameter) coreDepth 0 ∧
      color.2 ∈ TrimmedSlice.paletteSlice (Parameters.modulus parameter) coreDepth 0
    · simp only [SafePair.restrictPair, hc, and_self, if_true, TrimmedSlice.mixedPair, component]
    · simp only [SafePair.restrictPair, hc, if_false, component, mul_zero, Finset.sum_const_zero]
  have hmassPoint color := congrFun hmass color
  dsimp only
  rw [hmass]
  simp only [hmassPoint, convolution_mixture_apply, ← Finset.sum_sub_distrib, ← mul_sub]
  apply probability_profile_mixture_square_le_uniform
  intro sample
  exact restrictedPair_box_square_le parameter coreDepth radius boundary (starts sample) (sources sample)
    shiftBound cutoff width lower hlower hcore hboundary hradius (hstarts sample) (hsources sample) hclear

end
end AFT.GaussianSource

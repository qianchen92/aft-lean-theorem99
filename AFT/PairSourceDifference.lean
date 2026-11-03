import AFT.PairWindowTranslation
import AFT.SmoothingDifference

/-! # Genuine source differences of the integer-trimmed endpoint pair -/

namespace AFT.TrimmedSlice

open scoped BigOperators Classical
open SafeConvolution

/-- Moving only the source translates the anchor window; the true slice
denominator is unchanged at each fixed output pair. -/
theorem finite_window_source_square_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors) (start firstSource secondSource : ℤ) (width : ℕ) :
    (∑ color, (intervalAnchorLaw start width (colors color + firstSource) -
      intervalAnchorLaw start width (colors color + secondSource)) ^ 2) ≤
      2 * ((secondSource - firstSource).natAbs : ℝ) / (width : ℝ) ^ 2 := by
  have hinj' : Function.Injective (fun color => colors color + secondSource) := by
    intro a b h
    exact hinj (add_right_cancel h)
  have hh := finitePalette_sum_le_support (fun color => colors color + secondSource) hinj'
    (anchorInterval start width ∪ anchorInterval (start + (secondSource - firstSource)) width)
    (fun color => (intervalAnchorLaw (start + (secondSource - firstSource)) width color - intervalAnchorLaw start width color) ^ 2)
    (fun _ => sq_nonneg _) (fun color hout => by dsimp only; rw [anchorTranslation_zero_outside _ _ _ _ hout]; simp)
  have heq (color : ι) : intervalAnchorLaw (start + (secondSource - firstSource)) width (colors color + secondSource) =
      intervalAnchorLaw start width (colors color + firstSource) := by
    rw [intervalAnchorLaw_translate]
    congr 1
    ring
  simpa only [heq] using hh.trans (anchorTranslationSquare_le start (secondSource - firstSource) width)

theorem weightedIntegerWindow_source_square_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors) (modulus boundary lower : ℝ) (hl : 0 < lower)
    (start firstSource secondSource : ℤ) (width : ℕ) :
    (∑ color, (weightedIntegerWindow modulus boundary lower start firstSource width (colors color) -
      weightedIntegerWindow modulus boundary lower start secondSource width (colors color)) ^ 2) ≤
      2 * ((secondSource - firstSource).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) := by
  have hp (color : ι) : (weightedIntegerWindow modulus boundary lower start firstSource width (colors color) -
      weightedIntegerWindow modulus boundary lower start secondSource width (colors color)) ^ 2 ≤
      (1 / lower ^ 2) * (intervalAnchorLaw start width (colors color + firstSource) -
        intervalAnchorLaw start width (colors color + secondSource)) ^ 2 := by
    unfold weightedIntegerWindow
    rw [← sub_mul, mul_pow]
    have hh := pow_le_pow_left₀ (reciprocalSlice_nonneg modulus boundary lower hl (colors color))
      (reciprocalSlice_le modulus boundary lower hl (colors color)) 2
    calc
      _ ≤ (intervalAnchorLaw start width (colors color + firstSource) - intervalAnchorLaw start width (colors color + secondSource)) ^ 2 * (1 / lower) ^ 2 :=
        mul_le_mul_of_nonneg_left (by simpa only [one_div] using hh) (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑ color, (1 / lower ^ 2) * (intervalAnchorLaw start width (colors color + firstSource) - intervalAnchorLaw start width (colors color + secondSource)) ^ 2 :=
      Finset.sum_le_sum fun color _ => hp color
    _ = (1 / lower ^ 2) * ∑ color, (intervalAnchorLaw start width (colors color + firstSource) - intervalAnchorLaw start width (colors color + secondSource)) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / lower ^ 2) * (2 * ((secondSource - firstSource).natAbs : ℝ) / (width : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (finite_window_source_square_le colors hinj start firstSource secondSource width) (by positivity)
    _ = _ := by ring

/-- The full true fixed-endpoint source difference, including the original
integer endpoint mask, has no palette factor. -/
theorem averagedPair_source_fiber_square_le (modulus : ℕ) (boundary start firstSource secondSource shiftBound cutoff : ℤ)
    (width : ℕ) (lower : ℝ) (hl : 0 < lower)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hfirst : |firstSource| ≤ cutoff) (hsecond : |secondSource| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) (first : Fin modulus) :
    (∑ second, (averagedPair modulus boundary start firstSource width first second -
      averagedPair modulus boundary start secondSource width first second) ^ 2) ≤
      2 * ((secondSource - firstSource).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) := by
  let colors := fun second : Fin modulus => (first.val : ℤ) + second.val - ((modulus : ℤ) - 1)
  have hinj : Function.Injective colors := by
    intro a b h
    apply Fin.ext
    dsimp only [colors] at h
    omega
  calc
    _ ≤ ∑ second : Fin modulus,
        (weightedIntegerWindow modulus boundary lower start firstSource width (colors second) -
          weightedIntegerWindow modulus boundary lower start secondSource width (colors second)) ^ 2 := by
      apply Finset.sum_le_sum
      intro second _
      rw [averagedPair_eq_weightedIntegerWindow modulus boundary start firstSource shiftBound cutoff width lower hl hstarts hfirst hclear,
        averagedPair_eq_weightedIntegerWindow modulus boundary start secondSource shiftBound cutoff width lower hl hstarts hsecond hclear]
      split_ifs
      · exact le_rfl
      · simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using sq_nonneg
          (weightedIntegerWindow modulus boundary lower start firstSource width (colors second) -
            weightedIntegerWindow modulus boundary lower start secondSource width (colors second))
    _ ≤ _ := weightedIntegerWindow_source_square_le colors hinj modulus boundary lower hl start firstSource secondSource width

/-- Arbitrary actual body/sign mixtures retain the same source-difference
bound: their original probabilities are averaged before taking the norm. -/
theorem mixedPair_source_fiber_square_le {σ : Type*} [Fintype σ]
    (modulus : ℕ) (boundary firstSource secondSource shiftBound cutoff : ℤ)
    (starts : σ → ℤ) (sourceLaw : FiniteDist σ) (width : ℕ) (lower : ℝ) (hl : 0 < lower)
    (hstarts : ∀ sample shift, shift ∈ anchorInterval (starts sample) width → |shift| ≤ shiftBound)
    (hfirst : |firstSource| ≤ cutoff) (hsecond : |secondSource| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) (first : Fin modulus) :
    (∑ second, (mixedPair modulus boundary starts (fun _ => firstSource) sourceLaw.weight width first second -
      mixedPair modulus boundary starts (fun _ => secondSource) sourceLaw.weight width first second) ^ 2) ≤
      2 * ((secondSource - firstSource).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) := by
  have hh := probability_profile_mixture_square_le_uniform sourceLaw
    (fun sample second => averagedPair modulus boundary (starts sample) firstSource width first second -
      averagedPair modulus boundary (starts sample) secondSource width first second)
    (2 * ((secondSource - firstSource).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2))
    (fun sample => averagedPair_source_fiber_square_le modulus boundary (starts sample) firstSource secondSource shiftBound cutoff
      width lower hl (hstarts sample) hfirst hsecond hclear first)
  simpa only [mixedPair, mul_sub, Finset.sum_sub_distrib] using hh

end AFT.TrimmedSlice

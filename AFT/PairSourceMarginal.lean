import AFT.PairSourceDifference

/-! # Exact marginal control for source-dependent trimmed endpoint pairs -/

namespace AFT.TrimmedSlice

open scoped BigOperators Classical

/-- L1 translation on the actual finite palette is bounded by the two
integer interval edge strips, with no cyclic replacement. -/
theorem finite_window_source_l1_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors) (start firstSource secondSource : ℤ) (width : ℕ) :
    (∑ color, |intervalAnchorLaw start width (colors color + firstSource) -
      intervalAnchorLaw start width (colors color + secondSource)|) ≤
      2 * ((secondSource - firstSource).natAbs : ℝ) / width := by
  have hinj' : Function.Injective (fun color => colors color + secondSource) := by intro a b h; exact hinj (add_right_cancel h)
  have hh := finitePalette_sum_le_support (fun color => colors color + secondSource) hinj'
    (anchorInterval start width ∪ anchorInterval (start + (secondSource - firstSource)) width)
    (fun color => |intervalAnchorLaw (start + (secondSource - firstSource)) width color - intervalAnchorLaw start width color|)
    (fun _ => abs_nonneg _) (fun color hout => by dsimp only; rw [anchorTranslation_zero_outside _ _ _ _ hout, abs_zero])
  have heq (color : ι) : intervalAnchorLaw (start + (secondSource - firstSource)) width (colors color + secondSource) =
      intervalAnchorLaw start width (colors color + firstSource) := by
    rw [intervalAnchorLaw_translate]
    congr 1
    ring
  rw [interval_translation_l1] at hh
  simp only [heq] at hh
  exact hh.trans (div_le_div_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_left 2 (min_le_right width (secondSource - firstSource).natAbs)) (Nat.cast_nonneg width))

theorem weightedIntegerWindow_source_l1_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors) (modulus boundary lower : ℝ) (hl : 0 < lower)
    (start firstSource secondSource : ℤ) (width : ℕ) :
    (∑ color, |weightedIntegerWindow modulus boundary lower start firstSource width (colors color) -
      weightedIntegerWindow modulus boundary lower start secondSource width (colors color)|) ≤
      2 * ((secondSource - firstSource).natAbs : ℝ) / (lower * (width : ℝ)) := by
  have hp (color : ι) : |weightedIntegerWindow modulus boundary lower start firstSource width (colors color) -
      weightedIntegerWindow modulus boundary lower start secondSource width (colors color)| ≤
      lower⁻¹ * |intervalAnchorLaw start width (colors color + firstSource) -
        intervalAnchorLaw start width (colors color + secondSource)| := by
    unfold weightedIntegerWindow
    rw [← sub_mul, abs_mul, abs_of_nonneg (reciprocalSlice_nonneg modulus boundary lower hl _)]
    exact (mul_le_mul_of_nonneg_left (reciprocalSlice_le modulus boundary lower hl _) (abs_nonneg _)).trans_eq (mul_comm _ _)
  calc
    _ ≤ ∑ color, lower⁻¹ * |intervalAnchorLaw start width (colors color + firstSource) - intervalAnchorLaw start width (colors color + secondSource)| :=
      Finset.sum_le_sum fun color _ => hp color
    _ = lower⁻¹ * ∑ color, |intervalAnchorLaw start width (colors color + firstSource) - intervalAnchorLaw start width (colors color + secondSource)| := by rw [Finset.mul_sum]
    _ ≤ lower⁻¹ * (2 * ((secondSource - firstSource).natAbs : ℝ) / width) :=
      mul_le_mul_of_nonneg_left (finite_window_source_l1_le colors hinj start firstSource secondSource width) (inv_nonneg.mpr hl.le)
    _ = _ := by ring

theorem averagedPair_source_fiber_l1_le (modulus : ℕ) (boundary start firstSource secondSource shiftBound cutoff : ℤ)
    (width : ℕ) (lower : ℝ) (hl : 0 < lower)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hfirst : |firstSource| ≤ cutoff) (hsecond : |secondSource| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) (first : Fin modulus) :
    (∑ second, |averagedPair modulus boundary start firstSource width first second -
      averagedPair modulus boundary start secondSource width first second|) ≤
      2 * ((secondSource - firstSource).natAbs : ℝ) / (lower * (width : ℝ)) := by
  let colors := fun second : Fin modulus => (first.val : ℤ) + second.val - ((modulus : ℤ) - 1)
  have hinj : Function.Injective colors := by
    intro a b h
    apply Fin.ext
    dsimp only [colors] at h
    omega
  calc
    _ ≤ ∑ second : Fin modulus,
        |weightedIntegerWindow modulus boundary lower start firstSource width (colors second) -
          weightedIntegerWindow modulus boundary lower start secondSource width (colors second)| := by
      apply Finset.sum_le_sum
      intro second _
      rw [averagedPair_eq_weightedIntegerWindow modulus boundary start firstSource shiftBound cutoff width lower hl hstarts hfirst hclear,
        averagedPair_eq_weightedIntegerWindow modulus boundary start secondSource shiftBound cutoff width lower hl hstarts hsecond hclear]
      split_ifs
      · exact le_rfl
      · simpa only [sub_self, abs_zero] using abs_nonneg
          (weightedIntegerWindow modulus boundary lower start firstSource width (colors second) -
            weightedIntegerWindow modulus boundary lower start secondSource width (colors second))
    _ ≤ _ := weightedIntegerWindow_source_l1_le colors hinj modulus boundary lower hl start firstSource secondSource width

theorem mixedPair_source_fiber_l1_le {σ : Type*} [Fintype σ]
    (modulus : ℕ) (boundary firstSource secondSource shiftBound cutoff : ℤ)
    (starts : σ → ℤ) (sourceLaw : FiniteDist σ) (width : ℕ) (lower : ℝ) (hl : 0 < lower)
    (hstarts : ∀ sample shift, shift ∈ anchorInterval (starts sample) width → |shift| ≤ shiftBound)
    (hfirst : |firstSource| ≤ cutoff) (hsecond : |secondSource| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) (first : Fin modulus) :
    (∑ second, |mixedPair modulus boundary starts (fun _ => firstSource) sourceLaw.weight width first second -
      mixedPair modulus boundary starts (fun _ => secondSource) sourceLaw.weight width first second|) ≤
      2 * ((secondSource - firstSource).natAbs : ℝ) / (lower * (width : ℝ)) := by
  simp only [mixedPair, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ second, ∑ sample, |sourceLaw.weight sample *
        (averagedPair modulus boundary (starts sample) firstSource width first second -
          averagedPair modulus boundary (starts sample) secondSource width first second)| :=
      Finset.sum_le_sum fun second _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ sample, sourceLaw.weight sample * ∑ second,
        |averagedPair modulus boundary (starts sample) firstSource width first second -
          averagedPair modulus boundary (starts sample) secondSource width first second| := by
      rw [Finset.sum_comm]
      simp only [abs_mul, abs_of_nonneg (sourceLaw.nonneg _), Finset.mul_sum]
    _ ≤ ∑ sample, sourceLaw.weight sample * (2 * ((secondSource - firstSource).natAbs : ℝ) / (lower * (width : ℝ))) :=
      Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left
        (averagedPair_source_fiber_l1_le modulus boundary (starts sample) firstSource secondSource shiftBound cutoff width lower hl
          (hstarts sample) hfirst hsecond hclear first) (sourceLaw.nonneg sample)
    _ = _ := by rw [← Finset.sum_mul, sourceLaw.sum_one, one_mul]

end AFT.TrimmedSlice

import AFT.PairWindowTranslation

/-! # Exact endpoint-mask strip costs for an integer-window pair translation -/

namespace AFT.TrimmedSlice

open scoped BigOperators symmDiff

/-- Masking an integer window to an actual finite interval in each output. -/
noncomputable def maskedIntegerPair (modulus boundary lower : ℝ) (start source : ℤ) (width : ℕ)
    (coreStart : ℤ) (coreWidth : ℕ) (first second : ℤ) : ℝ :=
  if first ∈ anchorInterval coreStart coreWidth ∧ second ∈ anchorInterval coreStart coreWidth then
    weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋) else 0

/-- Restricting an injective finite palette to the two changed strips
counts at most twice the integer displacement. -/
theorem interval_change_count_le {ι : Type*} [Fintype ι] (colors : ι → ℤ)
    (hinj : Function.Injective colors) (start shift : ℤ) (width : ℕ) :
    (∑ color, if colors color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width then (1 : ℝ) else 0) ≤
      2 * (shift.natAbs : ℝ) := by
  have hh := finitePalette_sum_le_support colors hinj
    (anchorInterval start width ∆ anchorInterval (start + shift) width)
    (fun color => if color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width then (1 : ℝ) else 0)
    (fun _ => by dsimp only; split_ifs <;> norm_num) (fun color hout => by simp only [if_neg hout])
  have hcard : (∑ color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width,
      if color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width then (1 : ℝ) else 0) =
      2 * (min width shift.natAbs : ℝ) := by
    simp [anchorInterval_symmDiff_card]
  rw [hcard] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right width shift.natAbs) (by norm_num))

/-- Row energy of the exact denominator extension. -/
theorem weightedIntegerWindow_square_le {ι : Type*} [Fintype ι] (colors : ι → ℤ)
    (hinj : Function.Injective colors) (modulus boundary lower : ℝ) (hlower : 0 < lower)
    (start source : ℤ) (width : ℕ) :
    (∑ color, weightedIntegerWindow modulus boundary lower start source width (colors color) ^ 2) ≤
      1 / (lower ^ 2 * width) := by
  have hpoint (color : ι) : weightedIntegerWindow modulus boundary lower start source width (colors color) ^ 2 ≤
      (1 / lower ^ 2) * intervalAnchorLaw start width (colors color + source) ^ 2 := by
    have hnonneg := reciprocalSlice_nonneg modulus boundary lower hlower (colors color)
    have hu := reciprocalSlice_le modulus boundary lower hlower (colors color)
    have hh := mul_le_mul hu hu hnonneg (inv_nonneg.mpr hlower.le)
    have hh' : reciprocalSlice modulus boundary lower (colors color) ^ 2 ≤ 1 / lower ^ 2 := by
      simpa only [← sq, inv_pow, one_div] using hh
    unfold weightedIntegerWindow
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right hh' (sq_nonneg _)
  have hinj' : Function.Injective (fun color => colors color + source) := by
    intro a b heq
    exact hinj (add_right_cancel heq)
  calc
    _ ≤ ∑ color, (1 / lower ^ 2) * intervalAnchorLaw start width (colors color + source) ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = (1 / lower ^ 2) * ∑ color, intervalAnchorLaw start width (colors color + source) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / lower ^ 2) * (1 / (width : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_window_square_le _ hinj' start width) (by positivity)
    _ = _ := by ring

private theorem masked_difference_square (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (first second : ℝ) :
    ((if a ∧ b then first else 0) - (if c ∧ d then second else 0)) ^ 2 ≤
      2 * (first - second) ^ 2 +
      2 * (if (a ∧ ¬c) ∨ (c ∧ ¬a) then second ^ 2 else 0) +
      2 * (if (b ∧ ¬d) ∨ (d ∧ ¬b) then second ^ 2 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    simp only [ha, hb, hc, hd, not_true_eq_false, not_false_eq_true, and_self, and_true, and_false,
      or_self, or_false, false_or, if_true, if_false, sub_zero, zero_sub, neg_sq,
      mul_zero, add_zero] <;>
    nlinarith [sq_nonneg (first - 2 * second), sq_nonneg (first - second), sq_nonneg second]

/-- A shifted core mask changes only its actual one-dimensional symmetric
difference strips, in addition to the integer-sum window change. -/
theorem maskedIntegerPair_difference_square (modulus boundary lower : ℝ)
    (start source firstShift secondShift first second coreStart : ℤ) (width coreWidth : ℕ) :
    (maskedIntegerPair modulus boundary lower start source width coreStart coreWidth (first - firstShift) (second - secondShift) -
      maskedIntegerPair modulus boundary lower start source width coreStart coreWidth first second) ^ 2 ≤
      2 * (weightedIntegerWindow modulus boundary lower start source width
        ((first + second - ⌊modulus - 1⌋) - (firstShift + secondShift)) -
        weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋)) ^ 2 +
      2 * (if first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth then
        weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋) ^ 2 else 0) +
      2 * (if second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth then
        weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋) ^ 2 else 0) := by
  have hmem (value shift : ℤ) : value - shift ∈ anchorInterval coreStart coreWidth ↔
      value ∈ anchorInterval (coreStart + shift) coreWidth := by
    simp only [anchorInterval, Finset.mem_Ico]
    omega
  have htotal : first - firstShift + (second - secondShift) - ⌊modulus - 1⌋ =
      first + second - ⌊modulus - 1⌋ - (firstShift + secondShift) := by ring
  unfold maskedIntegerPair
  simp only [hmem, htotal]
  have hh := masked_difference_square
    (first ∈ anchorInterval (coreStart + firstShift) coreWidth) (second ∈ anchorInterval (coreStart + secondShift) coreWidth)
    (first ∈ anchorInterval coreStart coreWidth) (second ∈ anchorInterval coreStart coreWidth)
    (weightedIntegerWindow modulus boundary lower start source width
      (first + second - ⌊modulus - 1⌋ - (firstShift + secondShift)))
    (weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋))
  simpa only [Finset.mem_symmDiff, or_comm] using hh

/-- Both endpoint mask costs use one-fixed row energies. The final bound
contains precisely the physical window-edge, reciprocal-denominator, and
endpoint-strip terms. -/
theorem maskedIntegerPair_translation_square_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors)
    (modulus boundary lower : ℝ) (hlower : 0 < lower) (start source firstShift secondShift coreStart : ℤ)
    (width coreWidth : ℕ) :
    (∑ first, ∑ second,
      (maskedIntegerPair modulus boundary lower start source width coreStart coreWidth
        (colors first - firstShift) (colors second - secondShift) -
      maskedIntegerPair modulus boundary lower start source width coreStart coreWidth (colors first) (colors second)) ^ 2) ≤
      2 * (Fintype.card ι : ℝ) *
        (4 * ((firstShift + secondShift).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * ((firstShift + secondShift : ℤ) : ℝ) ^ 2 / (lower ^ 4 * width)) +
      4 * ((firstShift.natAbs : ℝ) + secondShift.natAbs) / (lower ^ 2 * width) := by
  let window (first second : ι) :=
    weightedIntegerWindow modulus boundary lower start source width (colors first + colors second - ⌊modulus - 1⌋)
  have hinjrow (first : ι) : Function.Injective (fun second => colors first + colors second - ⌊modulus - 1⌋) := by
    intro a b heq
    exact hinj (add_left_cancel (sub_left_inj.mp heq))
  have hinjcol (second : ι) : Function.Injective (fun first => colors first + colors second - ⌊modulus - 1⌋) := by
    intro a b heq
    exact hinj (add_right_cancel (sub_left_inj.mp heq))
  have hrows (first : ι) : (∑ second, window first second ^ 2) ≤ 1 / (lower ^ 2 * width) :=
    weightedIntegerWindow_square_le _ (hinjrow first) modulus boundary lower hlower start source width
  have hcols (second : ι) : (∑ first, window first second ^ 2) ≤ 1 / (lower ^ 2 * width) :=
    weightedIntegerWindow_square_le _ (hinjcol second) modulus boundary lower hlower start source width
  have hfirst : (∑ first, ∑ second, if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth
      then window first second ^ 2 else 0) ≤ 2 * (firstShift.natAbs : ℝ) / (lower ^ 2 * width) := by
    calc
      _ ≤ ∑ first, if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth
          then 1 / (lower ^ 2 * width) else 0 := by
        apply Finset.sum_le_sum
        intro first _
        split_ifs <;> simp_all only [Finset.sum_const_zero, le_refl]
      _ = (∑ first, if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth then (1 : ℝ) else 0) /
          (lower ^ 2 * width) := by simp only [Finset.sum_div, ite_div, zero_div, one_div]
      _ ≤ _ := div_le_div_of_nonneg_right (interval_change_count_le colors hinj coreStart firstShift coreWidth) (by positivity)
  have hsecond : (∑ first, ∑ second, if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth
      then window first second ^ 2 else 0) ≤ 2 * (secondShift.natAbs : ℝ) / (lower ^ 2 * width) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ second, if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth
          then 1 / (lower ^ 2 * width) else 0 := by
        apply Finset.sum_le_sum
        intro second _
        split_ifs <;> simp_all only [Finset.sum_const_zero, le_refl]
      _ = (∑ second, if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth then (1 : ℝ) else 0) /
          (lower ^ 2 * width) := by simp only [Finset.sum_div, ite_div, zero_div, one_div]
      _ ≤ _ := div_le_div_of_nonneg_right (interval_change_count_le colors hinj coreStart secondShift coreWidth) (by positivity)
  have hwindow : (∑ first, ∑ second,
      (weightedIntegerWindow modulus boundary lower start source width
        ((colors first + colors second - ⌊modulus - 1⌋) - (firstShift + secondShift)) - window first second) ^ 2) ≤
      (Fintype.card ι : ℝ) *
        (4 * ((firstShift + secondShift).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * ((firstShift + secondShift : ℤ) : ℝ) ^ 2 / (lower ^ 4 * width)) := by
    calc
      _ ≤ ∑ _first : ι, (4 * ((firstShift + secondShift).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * ((firstShift + secondShift : ℤ) : ℝ) ^ 2 / (lower ^ 4 * width)) :=
        Finset.sum_le_sum fun first _ => weightedIntegerWindow_translation_square_le _ (hinjrow first)
          modulus boundary lower hlower start source (firstShift + secondShift) width
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ ≤ ∑ first, ∑ second,
        (2 * (weightedIntegerWindow modulus boundary lower start source width
          ((colors first + colors second - ⌊modulus - 1⌋) - (firstShift + secondShift)) - window first second) ^ 2 +
        2 * (if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth then window first second ^ 2 else 0) +
        2 * (if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth then window first second ^ 2 else 0)) :=
      Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ =>
        maskedIntegerPair_difference_square modulus boundary lower start source firstShift secondShift (colors first) (colors second) coreStart width coreWidth
    _ ≤ _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hh := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hwindow (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 2)))
        (mul_le_mul_of_nonneg_left hsecond (by norm_num : (0 : ℝ) ≤ 2))
      exact hh.trans_eq (by ring)

end AFT.TrimmedSlice

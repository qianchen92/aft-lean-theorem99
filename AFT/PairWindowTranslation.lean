import AFT.TrimmedPair

/-! # Translation of the genuine integer pair window and its denominator -/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- A positive extension of the real reciprocal slice length. On every
allowed window it agrees exactly with the physical denominator; the
extension merely permits a global translation estimate. -/
noncomputable def reciprocalSlice (modulus boundary lower : ℝ) (sum : ℤ) : ℝ :=
  (max (modulus - 2 * boundary - |(sum : ℝ)|) lower)⁻¹

theorem reciprocalSlice_nonneg (modulus boundary lower : ℝ) (hlower : 0 < lower) (sum : ℤ) :
    0 ≤ reciprocalSlice modulus boundary lower sum := by
  unfold reciprocalSlice
  exact inv_nonneg.mpr ((le_max_right _ _).trans' hlower.le)

theorem reciprocalSlice_le (modulus boundary lower : ℝ) (hlower : 0 < lower) (sum : ℤ) :
    reciprocalSlice modulus boundary lower sum ≤ lower⁻¹ := by
  exact inv_anti₀ hlower (le_max_right _ _)

/-- The nonconstant denominator has Lipschitz cost 1/lower², derived
from the integer absolute-value slice length. -/
theorem reciprocalSlice_lipschitz (modulus boundary lower : ℝ) (hlower : 0 < lower) (first second : ℤ) :
    |reciprocalSlice modulus boundary lower first - reciprocalSlice modulus boundary lower second| ≤
      |(first : ℝ) - second| / lower ^ 2 := by
  let a := max (modulus - 2 * boundary - |(first : ℝ)|) lower
  let b := max (modulus - 2 * boundary - |(second : ℝ)|) lower
  have ha : lower ≤ a := le_max_right _ _
  have hb : lower ≤ b := le_max_right _ _
  have ha0 : 0 < a := hlower.trans_le ha
  have hb0 : 0 < b := hlower.trans_le hb
  have hdiff : |b - a| ≤ |(first : ℝ) - second| := by
    have hh := abs_max_sub_max_le_abs (modulus - 2 * boundary - |(second : ℝ)|)
      (modulus - 2 * boundary - |(first : ℝ)|) lower
    have heq : modulus - 2 * boundary - |(second : ℝ)| - (modulus - 2 * boundary - |(first : ℝ)|) =
        |(first : ℝ)| - |(second : ℝ)| := by ring
    rw [heq] at hh
    exact hh.trans (abs_abs_sub_abs_le _ _)
  have hprod : lower ^ 2 ≤ a * b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  change |a⁻¹ - b⁻¹| ≤ _
  have heq : |a⁻¹ - b⁻¹| = |b - a| / (a * b) := by
    rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_of_pos (mul_pos ha0 hb0)]
  rw [heq]
  exact (div_le_div_of_nonneg_right hdiff (mul_nonneg ha0.le hb0.le)).trans
    (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hlower) hprod)

noncomputable def weightedIntegerWindow (modulus boundary lower : ℝ) (start source : ℤ) (width : ℕ) (sum : ℤ) : ℝ :=
  intervalAnchorLaw start width (sum + source) * reciprocalSlice modulus boundary lower sum

/-- The pointwise difference separates the two changed window strips from
the exact reciprocal-denominator variation. -/
theorem weightedIntegerWindow_difference_square (modulus boundary lower : ℝ) (hlower : 0 < lower)
    (start source shift sum : ℤ) (width : ℕ) :
    (weightedIntegerWindow modulus boundary lower start source width (sum - shift) -
      weightedIntegerWindow modulus boundary lower start source width sum) ^ 2 ≤
      (2 / lower ^ 2) * (intervalAnchorLaw (start + shift) width (sum + source) - intervalAnchorLaw start width (sum + source)) ^ 2 +
        (2 * (shift : ℝ) ^ 2 / lower ^ 4) * intervalAnchorLaw start width (sum + source) ^ 2 := by
  let a := intervalAnchorLaw (start + shift) width (sum + source)
  let b := intervalAnchorLaw start width (sum + source)
  let u := reciprocalSlice modulus boundary lower (sum - shift)
  let v := reciprocalSlice modulus boundary lower sum
  have heq : weightedIntegerWindow modulus boundary lower start source width (sum - shift) -
      weightedIntegerWindow modulus boundary lower start source width sum = (a - b) * u + b * (u - v) := by
    unfold weightedIntegerWindow
    dsimp [a, b, u, v]
    rw [intervalAnchorLaw_translate]
    have harg : sum + source - shift = sum - shift + source := by omega
    rw [harg]
    ring
  rw [heq]
  have hu0 := reciprocalSlice_nonneg modulus boundary lower hlower (sum - shift)
  have hu := reciprocalSlice_le modulus boundary lower hlower (sum - shift)
  have hdiff := reciprocalSlice_lipschitz modulus boundary lower hlower (sum - shift) sum
  have harg : |((sum - shift : ℤ) : ℝ) - sum| = |(shift : ℝ)| := by push_cast; ring_nf; rw [abs_neg]
  rw [harg] at hdiff
  have husq : u ^ 2 ≤ 1 / lower ^ 2 := by
    have hh := mul_le_mul hu hu hu0 (inv_nonneg.mpr hlower.le)
    simpa only [← sq, inv_pow, one_div] using hh
  have hdiffsq : (u - v) ^ 2 ≤ (shift : ℝ) ^ 2 / lower ^ 4 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hdiff
    dsimp only [u, v]
    simpa only [← sq, sq_abs, div_pow, ← pow_mul] using hh
  have h1 := mul_le_mul_of_nonneg_left husq (sq_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hdiffsq (sq_nonneg b)
  have hsq := sq_nonneg ((a - b) * u - b * (u - v))
  change _ ≤ 2 / lower ^ 2 * (a - b) ^ 2 + 2 * (shift : ℝ) ^ 2 / lower ^ 4 * b ^ 2
  calc
    _ ≤ 2 * ((a - b) * u) ^ 2 + 2 * (b * (u - v)) ^ 2 := by nlinarith only [hsq]
    _ = 2 * ((a - b) ^ 2 * u ^ 2) + 2 * (b ^ 2 * (u - v) ^ 2) := by ring
    _ ≤ 2 * ((a - b) ^ 2 * (1 / lower ^ 2)) + 2 * (b ^ 2 * ((shift : ℝ) ^ 2 / lower ^ 4)) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

/-- Finite injective sampling of an integer window costs at most its full
counting energy 1/width. -/
theorem finite_window_square_le {ι : Type*} [Fintype ι] (colors : ι → ℤ)
    (hinj : Function.Injective colors) (start : ℤ) (width : ℕ) :
    (∑ color, intervalAnchorLaw start width (colors color) ^ 2) ≤ 1 / (width : ℝ) := by
  have hh := finitePalette_sum_le_support colors hinj (anchorInterval start width)
    (fun color => intervalAnchorLaw start width color ^ 2) (fun _ => sq_nonneg _)
    (fun color hout => by simp [intervalAnchorLaw, hout])
  exact hh.trans_eq (by
    have hsum : (∑ output ∈ anchorInterval start width, intervalAnchorLaw start width output ^ 2) =
        (width : ℝ) * ((width : ℝ)⁻¹) ^ 2 := by
      calc
        _ = ∑ _output ∈ anchorInterval start width, ((width : ℝ)⁻¹) ^ 2 := by
          apply Finset.sum_congr rfl
          intro output ho
          simp only [intervalAnchorLaw, if_pos ho]
        _ = _ := by simp only [Finset.sum_const, anchorInterval_card, nsmul_eq_mul]
    rw [hsum]
    by_cases hw : (width : ℝ) = 0
    · simp [hw]
    · field_simp)

/-- Full finite row bound for the genuine window-with-denominator kernel.
The first term is the window-edge cost and the second is the exact
reciprocal variation; neither introduces a palette factor. -/
theorem weightedIntegerWindow_translation_square_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors)
    (modulus boundary lower : ℝ) (hlower : 0 < lower) (start source shift : ℤ) (width : ℕ) :
    (∑ color, (weightedIntegerWindow modulus boundary lower start source width (colors color - shift) -
      weightedIntegerWindow modulus boundary lower start source width (colors color)) ^ 2) ≤
      4 * (shift.natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
        2 * (shift : ℝ) ^ 2 / (lower ^ 4 * width) := by
  have hinj' : Function.Injective (fun color => colors color + source) := by intro a b h; apply hinj; exact add_right_cancel h
  have hwindow := finitePalette_sum_le_support (fun color => colors color + source) hinj'
    (anchorInterval start width ∪ anchorInterval (start + shift) width)
    (fun color => (intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color) ^ 2)
    (fun _ => sq_nonneg _) (fun color hout => by dsimp only; rw [anchorTranslation_zero_outside _ _ _ _ hout]; simp)
  have hw := hwindow.trans (anchorTranslationSquare_le start shift width)
  have hbase := finite_window_square_le (fun color => colors color + source) hinj' start width
  calc
    _ ≤ ∑ color, ((2 / lower ^ 2) *
        (intervalAnchorLaw (start + shift) width (colors color + source) - intervalAnchorLaw start width (colors color + source)) ^ 2 +
      (2 * (shift : ℝ) ^ 2 / lower ^ 4) * intervalAnchorLaw start width (colors color + source) ^ 2) :=
      Finset.sum_le_sum fun color _ => weightedIntegerWindow_difference_square modulus boundary lower hlower start source shift (colors color) width
    _ = (2 / lower ^ 2) * (∑ color,
        (intervalAnchorLaw (start + shift) width (colors color + source) - intervalAnchorLaw start width (colors color + source)) ^ 2) +
      (2 * (shift : ℝ) ^ 2 / lower ^ 4) * (∑ color, intervalAnchorLaw start width (colors color + source) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (2 / lower ^ 2) * (2 * (shift.natAbs : ℝ) / (width : ℝ) ^ 2) +
      (2 * (shift : ℝ) ^ 2 / lower ^ 4) * (1 / (width : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hw (by positivity)) (mul_le_mul_of_nonneg_left hbase (by positivity))
    _ = _ := by ring

/-- On its physical window, the extended kernel is exactly the original
integer-sum endpoint law with the true endpoint mask. -/
theorem averagedPair_eq_weightedIntegerWindow (modulus : ℕ) (boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff)
    (first second : Fin modulus) :
    averagedPair modulus boundary start source width first second =
      if boundary ≤ (first.val : ℤ) ∧ (first.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
          boundary ≤ (second.val : ℤ) ∧ (second.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary then
        weightedIntegerWindow modulus boundary lower start source width
          ((first.val : ℤ) + second.val - ((modulus : ℤ) - 1)) else 0 := by
  rw [averagedPair_formula]
  let total : ℤ := (first.val : ℤ) + second.val - ((modulus : ℤ) - 1)
  have hmask : (first.val : ℤ) ∈ slice modulus boundary total ↔
      boundary ≤ (first.val : ℤ) ∧ (first.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
        boundary ≤ (second.val : ℤ) ∧ (second.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary := by
    rw [mem_slice]
    dsimp [total]
    omega
  by_cases hwindow : total + source ∈ anchorInterval start width
  · have hshift : |total| ≤ shiftBound + cutoff := by
      have hh := hstarts (total + source) hwindow
      have htriangle := abs_sub (total + source) source
      simp only [add_sub_cancel_right] at htriangle
      linarith
    have hden : lower ≤ (modulus : ℝ) - 2 * boundary - |(total : ℝ)| := by
      have hshift' : |(total : ℝ)| ≤ (shiftBound : ℝ) + cutoff := by exact_mod_cast hshift
      linarith
    have hdenInt : 0 ≤ (modulus : ℤ) - 2 * boundary - |total| := by
      have hh : (0 : ℝ) < (modulus : ℝ) - 2 * boundary - |(total : ℝ)| := hlower.trans_le hden
      have hh' : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - |total| := by exact_mod_cast hh
      omega
    have hcard : ((slice modulus boundary total).card : ℝ) = (modulus : ℝ) - 2 * boundary - |(total : ℝ)| := by
      rw [slice_card]
      exact_mod_cast Int.toNat_of_nonneg hdenInt
    change intervalAnchorLaw start width (total + source) * law modulus boundary total first.val = _
    unfold law
    simp only [hmask, hcard]
    split_ifs with hm
    · change intervalAnchorLaw start width (total + source) * _ =
        intervalAnchorLaw start width (total + source) * reciprocalSlice modulus boundary lower total
      rw [reciprocalSlice, max_eq_left hden]
    · simp
  · have hz : intervalAnchorLaw start width (total + source) = 0 := by simp only [intervalAnchorLaw, if_neg hwindow]
    change intervalAnchorLaw start width (total + source) * law modulus boundary total first.val = _
    rw [hz, zero_mul]
    split_ifs
    · change 0 = intervalAnchorLaw start width (total + source) * reciprocalSlice modulus boundary lower total
      rw [hz, zero_mul]
    · rfl

end AFT.TrimmedSlice

import AFT.MixedActivity

/-!
# Exact translation bounds for the public uniform interval anchors

The anchors are kept on the integer line. Their laws and the full finite
support of their translated difference are explicit; no cyclic-window
replacement or postulated matrix norm is used.
-/

namespace AFT

open scoped BigOperators symmDiff

/-- An integer interval of exactly `width` consecutive possible anchors. -/
def anchorInterval (start : ℤ) (width : ℕ) : Finset ℤ :=
  Finset.Ico start (start + width)

@[simp] theorem anchorInterval_card (start : ℤ) (width : ℕ) :
    (anchorInterval start width).card = width := by
  simp [anchorInterval, Int.card_Ico]

/-- The actual counting density of a uniform integer anchor interval. -/
noncomputable def intervalAnchorLaw (start : ℤ) (width : ℕ) (color : ℤ) : ℝ :=
  if color ∈ anchorInterval start width then (width : ℝ)⁻¹ else 0

theorem intervalAnchorLaw_nonneg (start color : ℤ) (width : ℕ) :
    0 ≤ intervalAnchorLaw start width color := by
  unfold intervalAnchorLaw
  split_ifs <;> positivity

theorem intervalAnchorLaw_mass (start : ℤ) (width : ℕ) (hwidth : width ≠ 0) :
    (∑ color ∈ anchorInterval start width, intervalAnchorLaw start width color) = 1 := by
  have hne : (width : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hwidth
  simp [intervalAnchorLaw, hne]

theorem intervalAnchorLaw_bound (start color : ℤ) (width : ℕ) :
    intervalAnchorLaw start width color ≤ (width : ℝ)⁻¹ := by
  unfold intervalAnchorLaw
  split_ifs <;> simp

/-- Translating a whole interval translates its law exactly. -/
theorem intervalAnchorLaw_translate (start shift color : ℤ) (width : ℕ) :
    intervalAnchorLaw (start + shift) width color =
      intervalAnchorLaw start width (color - shift) := by
  unfold intervalAnchorLaw anchorInterval
  have hmem : color ∈ Finset.Ico (start + shift) (start + shift + width) ↔
      color - shift ∈ Finset.Ico start (start + width) := by
    simp only [Finset.mem_Ico]
    omega
  simp only [hmem]

/-- Exact size of the overlap, including shifts longer than the interval. -/
theorem anchorInterval_inter_card (start shift : ℤ) (width : ℕ) :
    (anchorInterval start width ∩ anchorInterval (start + shift) width).card =
      width - min width shift.natAbs := by
  rw [anchorInterval, anchorInterval, Finset.Ico_inter_Ico, Int.card_Ico]
  have habs := Int.natCast_natAbs shift
  by_cases hs : 0 ≤ shift
  · rw [abs_of_nonneg hs] at habs
    omega
  · rw [abs_of_neg (lt_of_not_ge hs)] at habs
    omega

/-- Exactly two edge strips are changed by a translation. -/
theorem anchorInterval_symmDiff_card (start shift : ℤ) (width : ℕ) :
    (anchorInterval start width ∆ anchorInterval (start + shift) width).card =
      2 * min width shift.natAbs := by
  let first := anchorInterval start width
  let second := anchorInterval (start + shift) width
  have hd : Disjoint (first \ second) (second \ first) := by
    apply Finset.disjoint_left.mpr
    intro color hc hd
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_sdiff.mp hd).1
  change ((first \ second) ∪ (second \ first)).card = _
  rw [Finset.card_union_of_disjoint hd, Finset.card_sdiff, Finset.card_sdiff,
    Finset.inter_comm second first]
  simp only [first, second, anchorInterval_card, anchorInterval_inter_card]
  omega

/-- Full squared counting norm of the translated anchor difference. Every
nonzero coordinate is included in the displayed finite union. -/
noncomputable def anchorTranslationSquare (start shift : ℤ) (width : ℕ) : ℝ :=
  ∑ color ∈ anchorInterval start width ∪ anchorInterval (start + shift) width,
    (intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color) ^ 2

/-- Outside this union the translated difference is exactly zero. -/
theorem anchorTranslation_zero_outside (start shift color : ℤ) (width : ℕ)
    (houtside : color ∉ anchorInterval start width ∪ anchorInterval (start + shift) width) :
    intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color = 0 := by
  simp only [Finset.mem_union, not_or] at houtside
  simp [intervalAnchorLaw, houtside.1, houtside.2]

/-- The squared counting norm is exactly `2 min(|shift|,width) / width²`. -/
theorem anchorTranslationSquare_eq (start shift : ℤ) (width : ℕ) :
    anchorTranslationSquare start shift width =
      2 * (min width shift.natAbs : ℝ) / (width : ℝ) ^ 2 := by
  have hrestrict : anchorTranslationSquare start shift width =
      ∑ color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width,
        (intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color) ^ 2 := by
    symm
    apply Finset.sum_subset Finset.symmDiff_subset_union
    intro color _ hnot
    simp only [Finset.mem_symmDiff, not_or, not_and] at hnot
    unfold intervalAnchorLaw
    split_ifs <;> simp_all
  rw [hrestrict]
  have hrow (color : ℤ)
      (hc : color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width) :
      (intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color) ^ 2 =
        ((width : ℝ)⁻¹) ^ 2 := by
    rcases Finset.mem_symmDiff.mp hc with ⟨hfirst, hsecond⟩ | ⟨hsecond, hfirst⟩ <;>
      simp [intervalAnchorLaw, hfirst, hsecond]
  calc
    _ = ∑ _color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width,
        ((width : ℝ)⁻¹) ^ 2 := Finset.sum_congr rfl hrow
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, anchorInterval_symmDiff_card,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_min]
      ring

/-- The Hilbert estimate used in the local primary inverse. -/
theorem anchorTranslationSquare_le (start shift : ℤ) (width : ℕ) :
    anchorTranslationSquare start shift width ≤ 2 * (shift.natAbs : ℝ) / (width : ℝ) ^ 2 := by
  rw [anchorTranslationSquare_eq]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hm : (min width shift.natAbs : ℝ) ≤ shift.natAbs := by
    exact_mod_cast min_le_right width shift.natAbs
  linarith

/-- The uniform row bound does not lose a factor of the palette size. -/
theorem anchorTranslation_row_bound (start shift color : ℤ) (width : ℕ) :
    |intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color| ≤
      (width : ℝ)⁻¹ := by
  unfold intervalAnchorLaw
  split_ifs <;> simp

/-- The left anchor used below the palette midpoint stays in the safe
integer interval after every allowed source displacement. -/
theorem publicAnchor_left_safe (modulus width color offset shift safeMargin maxShift : ℤ)
    (hmodulus : 6 * width + 1 ≤ modulus) (hcolor : 0 ≤ color)
    (hhalf : 2 * color ≤ modulus - 1) (hoffsetLower : width ≤ offset)
    (hoffsetUpper : offset < 2 * width) (hshift : |shift| ≤ maxShift)
    (hmargin : safeMargin + maxShift ≤ width) :
    safeMargin ≤ modulus - 1 - color - offset + shift ∧
      modulus - 1 - color - offset + shift < modulus - safeMargin := by
  have hs := abs_le.mp hshift
  omega

/-- The right anchor used above the midpoint obeys the same safe bounds. -/
theorem publicAnchor_right_safe (modulus width color offset shift safeMargin maxShift : ℤ)
    (hmodulus : 6 * width + 1 ≤ modulus) (hcolor : color < modulus)
    (hhalf : modulus - 1 ≤ 2 * color) (hoffsetLower : width ≤ offset)
    (hoffsetUpper : offset < 2 * width) (hshift : |shift| ≤ maxShift)
    (hmargin : safeMargin + maxShift ≤ width) :
    safeMargin ≤ modulus - 1 - color + offset + shift ∧
      modulus - 1 - color + offset + shift < modulus - safeMargin := by
  have hs := abs_le.mp hshift
  omega

section ActualAnchorMatrix

variable {ι : Type*} [Fintype ι]

/-- One translated anchor row minus the original row. -/
noncomputable def intervalAnchorDifference (starts : ι → ℤ) (shift : ℤ) (width : ℕ)
    (input : ι) (output : ℤ) : ℝ :=
  intervalAnchorLaw (starts input + shift) width output -
    intervalAnchorLaw (starts input) width output

/-- Explicit finite support covering every row of the actual anchor matrix. -/
noncomputable def anchorMatrixSupport (starts : ι → ℤ) (shift : ℤ) (width : ℕ) : Finset ℤ :=
  Finset.univ.biUnion fun input =>
    anchorInterval (starts input) width ∪ anchorInterval (starts input + shift) width

/-- Every row's full squared norm on the common output palette is still the
exact interval norm; enlarging to the common support adds only zeros. -/
theorem intervalAnchorDifference_row_square (starts : ι → ℤ) (shift : ℤ) (width : ℕ)
    (input : ι) :
    (∑ output ∈ anchorMatrixSupport starts shift width,
      intervalAnchorDifference starts shift width input output ^ 2) =
      anchorTranslationSquare (starts input) shift width := by
  symm
  apply Finset.sum_subset
  · intro output hout
    exact Finset.mem_biUnion.mpr ⟨input, Finset.mem_univ _, hout⟩
  · intro output _ hout
    simp [anchorTranslation_zero_outside (starts input) shift output width hout]

/-- Weighted Cauchy--Schwarz for a genuinely signed finite anchor row. -/
theorem signedAnchorRow_sq_le (primary profile row : ι → ℝ)
    (hp : ∀ input, 0 < primary input) :
    (∑ input, row input * profile input) ^ 2 ≤
      (∑ input, primary input * row input ^ 2) * profileSquareNorm primary profile := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro input _
    exact mul_nonneg (le_of_lt (hp input)) (sq_nonneg _)
  · intro input _
    exact div_nonneg (sq_nonneg _) (le_of_lt (hp input))
  · intro input _
    have hne := ne_of_gt (hp input)
    field_simp

/-- The actual interval anchor difference matrix has the counting L2
operator bound used in V7, derived from its edge strips. -/
theorem intervalAnchorDifference_counting_bound (starts : ι → ℤ) (shift : ℤ) (width : ℕ)
    (primary profile : ι → ℝ) (hp : ∀ input, 0 < primary input)
    (hmass : ∑ input, primary input = 1) :
    (∑ output ∈ anchorMatrixSupport starts shift width,
      (∑ input, intervalAnchorDifference starts shift width input output * profile input) ^ 2) ≤
      (2 * (shift.natAbs : ℝ) / (width : ℝ) ^ 2) * profileSquareNorm primary profile := by
  have hn := profileSquareNorm_nonneg primary profile (fun input => le_of_lt (hp input))
  calc
    _ ≤ ∑ output ∈ anchorMatrixSupport starts shift width,
        (∑ input, primary input * intervalAnchorDifference starts shift width input output ^ 2) *
          profileSquareNorm primary profile := by
      exact Finset.sum_le_sum fun output _ => signedAnchorRow_sq_le primary profile _ hp
    _ = (∑ input, primary input *
        ∑ output ∈ anchorMatrixSupport starts shift width,
          intervalAnchorDifference starts shift width input output ^ 2) *
        profileSquareNorm primary profile := by
      rw [← Finset.sum_mul, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ (∑ input, primary input * (2 * (shift.natAbs : ℝ) / (width : ℝ) ^ 2)) *
        profileSquareNorm primary profile := by
      apply mul_le_mul_of_nonneg_right _ hn
      apply Finset.sum_le_sum
      intro input _
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (hp input))
      rw [intervalAnchorDifference_row_square]
      exact anchorTranslationSquare_le (starts input) shift width
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

/-- Converting to any positive output profile reference costs exactly its
reciprocal lower bound. With `lower = c/q`, this gives the desired
`2 q |shift| / (c width²)` squared operator bound. -/
theorem intervalAnchorDifference_profile_bound (starts : ι → ℤ) (shift : ℤ) (width : ℕ)
    (primary profile : ι → ℝ) (outputReference : ℤ → ℝ) (lower : ℝ)
    (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1)
    (hlower : 0 < lower)
    (hout : ∀ output ∈ anchorMatrixSupport starts shift width, lower ≤ outputReference output) :
    (∑ output ∈ anchorMatrixSupport starts shift width,
      (∑ input, intervalAnchorDifference starts shift width input output * profile input) ^ 2 /
        outputReference output) ≤
      (2 * (shift.natAbs : ℝ) / ((width : ℝ) ^ 2 * lower)) *
        profileSquareNorm primary profile := by
  calc
    _ ≤ ∑ output ∈ anchorMatrixSupport starts shift width,
        (∑ input, intervalAnchorDifference starts shift width input output * profile input) ^ 2 /
          lower := by
      exact Finset.sum_le_sum fun output houtput =>
        div_le_div_of_nonneg_left (sq_nonneg _) hlower (hout output houtput)
    _ = (∑ output ∈ anchorMatrixSupport starts shift width,
        (∑ input, intervalAnchorDifference starts shift width input output * profile input) ^ 2) /
          lower := by rw [Finset.sum_div]
    _ ≤ ((2 * (shift.natAbs : ℝ) / (width : ℝ) ^ 2) * profileSquareNorm primary profile) /
          lower := div_le_div_of_nonneg_right
            (intervalAnchorDifference_counting_bound starts shift width primary profile hp hmass)
            (le_of_lt hlower)
    _ = _ := by ring

/-- The real finite primary profile has L1 norm at most its weighted L2
norm, because its reference probabilities sum to one. -/
theorem profile_l1_le_sqrt (primary profile : ι → ℝ)
    (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1) :
    (∑ input, |profile input|) ≤ Real.sqrt (profileSquareNorm primary profile) := by
  apply Real.le_sqrt_of_sq_le
  have h : (∑ input, |profile input|) ^ 2 ≤
      (∑ input, primary input) * profileSquareNorm primary profile := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro input _
      exact le_of_lt (hp input)
    · intro input _
      exact div_nonneg (sq_nonneg _) (le_of_lt (hp input))
    · intro input _
      have hne := ne_of_gt (hp input)
      rw [sq_abs]
      field_simp
  simpa only [hmass, one_mul] using h

/-- The actual anchor difference's density row costs `1 / (lower * width)`
from profile L2 to supremum. This yields V7's `O(q / width)` estimate. -/
theorem intervalAnchorDifference_density_row_bound (starts : ι → ℤ) (shift output : ℤ)
    (width : ℕ) (primary profile : ι → ℝ) (outputReference lower : ℝ)
    (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1)
    (hlower : 0 < lower) (hout : lower ≤ outputReference) :
    |(∑ input, intervalAnchorDifference starts shift width input output * profile input) /
      outputReference| ≤ (1 / ((width : ℝ) * lower)) * Real.sqrt (profileSquareNorm primary profile) := by
  have hsum : |∑ input, intervalAnchorDifference starts shift width input output * profile input| ≤
      (width : ℝ)⁻¹ * Real.sqrt (profileSquareNorm primary profile) := by
    calc
      _ ≤ ∑ input, |intervalAnchorDifference starts shift width input output * profile input| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ input, (width : ℝ)⁻¹ * |profile input| := by
        apply Finset.sum_le_sum
        intro input _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (anchorTranslation_row_bound (starts input) shift output width) (abs_nonneg _)
      _ = (width : ℝ)⁻¹ * ∑ input, |profile input| := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (profile_l1_le_sqrt primary profile hp hmass) (by positivity)
  rw [abs_div, abs_of_pos (hlower.trans_le hout)]
  calc
    _ ≤ |∑ input, intervalAnchorDifference starts shift width input output * profile input| / lower :=
      div_le_div_of_nonneg_left (abs_nonneg _) hlower hout
    _ ≤ ((width : ℝ)⁻¹ * Real.sqrt (profileSquareNorm primary profile)) / lower :=
      div_le_div_of_nonneg_right hsum (le_of_lt hlower)
    _ = _ := by ring

/-- A finite palette embedded into the integer line cannot increase a
nonnegative finite-support counting sum. -/
theorem finitePalette_sum_le_support (colors : ι → ℤ) (hinj : Function.Injective colors)
    (support : Finset ℤ) (value : ℤ → ℝ) (hn : ∀ output, 0 ≤ value output)
    (hz : ∀ output ∉ support, value output = 0) :
    (∑ color, value (colors color)) ≤ ∑ output ∈ support, value output := by
  classical
  have hsum : (∑ output ∈ support, value output) =
      ∑ output ∈ Finset.univ.image colors ∪ support, value output := by
    exact Finset.sum_subset Finset.subset_union_right (fun output _ hout => hz output hout)
  calc
    _ = ∑ output ∈ Finset.univ.image colors, value output := by
      rw [Finset.sum_image]
      intro first _ second _ heq
      exact hinj heq
    _ ≤ ∑ output ∈ Finset.univ.image colors ∪ support, value output := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun output _ _ => hn output)
    _ = _ := hsum.symm

/-- Restricting the actual integer anchor matrix to an injectively encoded
finite palette preserves its weighted-profile estimate. -/
theorem finitePalette_anchorProfile_bound (colors starts : ι → ℤ)
    (hinj : Function.Injective colors) (shift : ℤ) (width : ℕ)
    (primary profile : ι → ℝ) (lower : ℝ)
    (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1)
    (hlower : 0 < lower) (hout : ∀ output, lower ≤ primary output) :
    profileSquareNorm primary (fun output =>
      ∑ input, intervalAnchorDifference starts shift width input (colors output) * profile input) ≤
      (2 * (shift.natAbs : ℝ) / ((width : ℝ) ^ 2 * lower)) *
        profileSquareNorm primary profile := by
  have hcount : (∑ output,
      (∑ input, intervalAnchorDifference starts shift width input (colors output) * profile input) ^ 2) ≤
      ∑ output ∈ anchorMatrixSupport starts shift width,
      (∑ input, intervalAnchorDifference starts shift width input output * profile input) ^ 2 := by
    apply finitePalette_sum_le_support colors hinj (anchorMatrixSupport starts shift width)
      (fun output => (∑ input, intervalAnchorDifference starts shift width input output * profile input) ^ 2)
      (fun _ => sq_nonneg _)
    intro output hout
    have hrow (input : ι) : intervalAnchorDifference starts shift width input output = 0 := by
      apply anchorTranslation_zero_outside
      intro hmem
      exact hout (Finset.mem_biUnion.mpr ⟨input, Finset.mem_univ _, hmem⟩)
    simp [hrow]
  calc
    _ ≤ ∑ output,
        (∑ input, intervalAnchorDifference starts shift width input (colors output) * profile input) ^ 2 /
          lower := by
      exact Finset.sum_le_sum fun output _ =>
        div_le_div_of_nonneg_left (sq_nonneg _) hlower (hout output)
    _ = (∑ output,
        (∑ input, intervalAnchorDifference starts shift width input (colors output) * profile input) ^ 2) /
          lower := by rw [Finset.sum_div]
    _ ≤ ((2 * (shift.natAbs : ℝ) / (width : ℝ) ^ 2) * profileSquareNorm primary profile) /
          lower := div_le_div_of_nonneg_right
            (hcount.trans (intervalAnchorDifference_counting_bound starts shift width primary profile hp hmass))
            (le_of_lt hlower)
    _ = _ := by ring

omit [Fintype ι] in
/-- Both interval laws have mass one on their full union; hence an actual
translation row has total mass zero. -/
theorem intervalAnchorDifference_mass (starts : ι → ℤ) (shift : ℤ) (width : ℕ)
    (hwidth : width ≠ 0) (input : ι) :
    (∑ output ∈ anchorInterval (starts input) width ∪ anchorInterval (starts input + shift) width,
      intervalAnchorDifference starts shift width input output) = 0 := by
  have hfirst : (∑ output ∈ anchorInterval (starts input) width,
      intervalAnchorLaw (starts input) width output) =
      ∑ output ∈ anchorInterval (starts input) width ∪ anchorInterval (starts input + shift) width,
        intervalAnchorLaw (starts input) width output := by
    exact Finset.sum_subset Finset.subset_union_left
      (fun output _ hout => by simp [intervalAnchorLaw, hout])
  have hsecond : (∑ output ∈ anchorInterval (starts input + shift) width,
      intervalAnchorLaw (starts input + shift) width output) =
      ∑ output ∈ anchorInterval (starts input) width ∪ anchorInterval (starts input + shift) width,
        intervalAnchorLaw (starts input + shift) width output := by
    exact Finset.sum_subset Finset.subset_union_right
      (fun output _ hout => by simp [intervalAnchorLaw, hout])
  simp only [intervalAnchorDifference, Finset.sum_sub_distrib, ← hfirst, ← hsecond,
    intervalAnchorLaw_mass _ _ hwidth, sub_self]

/-- A finite palette containing the support preserves the exact signed sum. -/
theorem finitePalette_sum_eq_support (colors : ι → ℤ) (hinj : Function.Injective colors)
    (support : Finset ℤ) (value : ℤ → ℝ) (hcover : support ⊆ Finset.univ.image colors)
    (hz : ∀ output ∉ support, value output = 0) :
    (∑ color, value (colors color)) = ∑ output ∈ support, value output := by
  classical
  rw [← Finset.sum_image]
  · symm
    exact Finset.sum_subset hcover (fun output _ hout => hz output hout)
  · intro first _ second _ heq
    exact hinj heq

/-- The actual finite-palette row has mass zero, using full support
coverage rather than assuming mass preservation of the operator. -/
theorem finitePalette_anchorDifference_mass (colors starts : ι → ℤ)
    (hinj : Function.Injective colors) (shift : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (input : ι)
    (hcover : anchorInterval (starts input) width ∪ anchorInterval (starts input + shift) width ⊆
      Finset.univ.image colors) :
    (∑ output, intervalAnchorDifference starts shift width input (colors output)) = 0 := by
  rw [finitePalette_sum_eq_support colors hinj _ _ hcover]
  · exact intervalAnchorDifference_mass starts shift width hwidth input
  · intro output hout
    exact anchorTranslation_zero_outside (starts input) shift output width hout

end ActualAnchorMatrix

end AFT

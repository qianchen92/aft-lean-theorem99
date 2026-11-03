import AFT.Anchor

/-!
# Actual trimmed pair slices and averaging over the public interval

The slice is the intersection of the two endpoint safety inequalities.
Its cardinality and its counting probability law are computed exactly.
-/

namespace AFT.TrimmedSlice

open scoped BigOperators symmDiff

/-- Both endpoint colors must avoid the boundary strip. -/
def slice (modulus boundary shift : ℤ) : Finset ℤ :=
  Finset.Ico (boundary + max shift 0) (modulus - boundary + min shift 0)

theorem mem_slice (modulus boundary shift color : ℤ) :
    color ∈ slice modulus boundary shift ↔
      boundary ≤ color ∧ color ≤ modulus - 1 - boundary ∧
      boundary ≤ modulus - 1 + shift - color ∧
      modulus - 1 + shift - color ≤ modulus - 1 - boundary := by
  simp only [slice, Finset.mem_Ico]
  omega

/-- The exact cardinality printed in the chart construction. -/
theorem slice_card (modulus boundary shift : ℤ) :
    (slice modulus boundary shift).card = (modulus - 2 * boundary - |shift|).toNat := by
  rw [slice, Int.card_Ico]
  congr 1
  by_cases hs : 0 ≤ shift
  · rw [abs_of_nonneg hs]
    omega
  · rw [abs_of_neg (lt_of_not_ge hs)]
    omega

noncomputable def law (modulus boundary shift color : ℤ) : ℝ :=
  if color ∈ slice modulus boundary shift then ((slice modulus boundary shift).card : ℝ)⁻¹ else 0

theorem law_nonneg (modulus boundary shift color : ℤ) : 0 ≤ law modulus boundary shift color := by
  unfold law
  split_ifs <;> positivity

theorem law_mass (modulus boundary shift : ℤ) (hwidth : 2 * boundary + |shift| < modulus) :
    ∑ color ∈ slice modulus boundary shift, law modulus boundary shift color = 1 := by
  have hcard : (slice modulus boundary shift).card ≠ 0 := by
    rw [slice_card]
    omega
  have hn : ((slice modulus boundary shift).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
  simp [law, hn]

theorem law_zero_outside (modulus boundary shift color : ℤ)
    (hout : color < boundary ∨ modulus - 1 - boundary < color) :
    law modulus boundary shift color = 0 := by
  have hh : color ∉ slice modulus boundary shift := by rw [mem_slice]; omega
  simp [law, hh]

/-- Every actual trimmed law has the advertised supremum bound. -/
theorem law_le_of_shift_bound (modulus boundary shift shiftBound color : ℤ)
    (hshift : |shift| ≤ shiftBound) (hwidth : 2 * boundary + shiftBound < modulus) :
    law modulus boundary shift color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound) := by
  have hcard : ((slice modulus boundary shift).card : ℤ) = modulus - 2 * boundary - |shift| := by
    rw [slice_card, Int.toNat_of_nonneg (by omega)]
  have hcardReal : ((slice modulus boundary shift).card : ℝ) =
      (modulus : ℝ) - 2 * boundary - |(shift : ℝ)| := by exact_mod_cast hcard
  have hshiftReal : |(shift : ℝ)| ≤ shiftBound := by exact_mod_cast hshift
  have hwidthReal : 0 < (modulus : ℝ) - 2 * boundary - shiftBound := by exact_mod_cast (show 0 < modulus - 2 * boundary - shiftBound by omega)
  unfold law
  split_ifs
  · rw [hcardReal, ← one_div]
    exact one_div_le_one_div_of_le hwidthReal (by linarith)
  · positivity

/-- Average the slice over the actual finite public uniform offset interval. -/
noncomputable def intervalMixture (start : ℤ) (width : ℕ) (kernel : ℤ → ℝ) : ℝ :=
  ∑ shift ∈ anchorInterval start width, intervalAnchorLaw start width shift * kernel shift

/-- The full counting L1 difference of translated interval laws. -/
theorem interval_translation_l1 (start shift : ℤ) (width : ℕ) :
    (∑ color ∈ anchorInterval start width ∪ anchorInterval (start + shift) width,
      |intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color|) =
      2 * (min width shift.natAbs : ℝ) / width := by
  have hrestrict : (∑ color ∈ anchorInterval start width ∪ anchorInterval (start + shift) width,
      |intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color|) =
      ∑ color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width,
        |intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color| := by
    symm
    apply Finset.sum_subset Finset.symmDiff_subset_union
    intro color _ hnot
    simp only [Finset.mem_symmDiff, not_or, not_and] at hnot
    unfold intervalAnchorLaw
    split_ifs <;> simp_all
  rw [hrestrict]
  have hrow (color : ℤ)
      (hc : color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width) :
      |intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color| =
        (width : ℝ)⁻¹ := by
    rcases Finset.mem_symmDiff.mp hc with ⟨hfirst, hsecond⟩ | ⟨hsecond, hfirst⟩ <;>
      simp [intervalAnchorLaw, hfirst, hsecond]
  calc
    _ = ∑ _color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width,
        (width : ℝ)⁻¹ := Finset.sum_congr rfl hrow
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, anchorInterval_symmDiff_card,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_min]
      ring

/-- A signed mass-zero measure tests a kernel in `[0,M]` with half its L1
mass. This is the TV contraction used for the shifted slice. -/
theorem balanced_kernel_bound {ι : Type*} (support : Finset ι) (signed kernel : ι → ℝ)
    (upper : ℝ) (hmass : ∑ point ∈ support, signed point = 0)
    (hkernel : ∀ point ∈ support, 0 ≤ kernel point ∧ kernel point ≤ upper) :
    |∑ point ∈ support, signed point * kernel point| ≤
      (upper / 2) * ∑ point ∈ support, |signed point| := by
  have heq : (∑ point ∈ support, signed point * kernel point) =
      ∑ point ∈ support, signed point * (kernel point - upper / 2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, zero_mul, sub_zero]
  rw [heq, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro point hpoint
  rw [abs_mul]
  have hk : |kernel point - upper / 2| ≤ upper / 2 := abs_le.mpr (by constructor <;> linarith [(hkernel point hpoint).1, (hkernel point hpoint).2])
  nlinarith [mul_le_mul_of_nonneg_left hk (abs_nonneg (signed point))]

/-- Shifting the real public offset interval through `shift` changes the
averaged bounded nonnegative kernel by at most `M |shift| / width`. -/
theorem intervalMixture_shift_bound (start shift : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (kernel : ℤ → ℝ) (upper : ℝ) (hupper : 0 ≤ upper)
    (hkernel : ∀ point ∈ anchorInterval start width ∪ anchorInterval (start + shift) width,
      0 ≤ kernel point ∧ kernel point ≤ upper) :
    |intervalMixture (start + shift) width kernel - intervalMixture start width kernel| ≤
      upper * (shift.natAbs : ℝ) / width := by
  let support := anchorInterval start width ∪ anchorInterval (start + shift) width
  have hfirst (test : ℤ → ℝ) :
      (∑ point ∈ support, intervalAnchorLaw start width point * test point) = intervalMixture start width test := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro point _ hout
    simp [intervalAnchorLaw, hout]
  have hsecond (test : ℤ → ℝ) :
      (∑ point ∈ support, intervalAnchorLaw (start + shift) width point * test point) =
        intervalMixture (start + shift) width test := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro point _ hout
    simp [intervalAnchorLaw, hout]
  have hmass : (∑ point ∈ support,
      (intervalAnchorLaw (start + shift) width point - intervalAnchorLaw start width point)) = 0 := by
    have h1 := hfirst (fun _ => 1)
    have h2 := hsecond (fun _ => 1)
    simp only [mul_one, intervalMixture, intervalAnchorLaw_mass _ _ hwidth] at h1 h2
    rw [Finset.sum_sub_distrib, h1, h2, sub_self]
  have hb := balanced_kernel_bound support
    (fun point => intervalAnchorLaw (start + shift) width point - intervalAnchorLaw start width point)
    kernel upper hmass hkernel
  have heq : (∑ point ∈ support,
      (intervalAnchorLaw (start + shift) width point - intervalAnchorLaw start width point) * kernel point) =
      intervalMixture (start + shift) width kernel - intervalMixture start width kernel := by
    simp only [sub_mul, Finset.sum_sub_distrib, hfirst, hsecond]
  rw [heq] at hb
  dsimp [support] at hb
  rw [interval_translation_l1] at hb
  have hmin : (min width shift.natAbs : ℝ) ≤ shift.natAbs := min_le_right _ _
  have hh := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hmin (Nat.cast_nonneg width)) hupper
  calc
    _ ≤ (upper / 2) * (2 * (min width shift.natAbs : ℝ) / width) := hb
    _ = upper * ((min width shift.natAbs : ℝ) / width) := by ring
    _ ≤ upper * ((shift.natAbs : ℝ) / width) := hh
    _ = _ := by ring

/-- Translating the protected source is exactly a translation of the
public offset averaging measure; it introduces no independent source copy. -/
theorem intervalMixture_translate (start source : ℤ) (width : ℕ) (kernel : ℤ → ℝ) :
    intervalMixture start width (fun shift => kernel (shift - source)) =
      intervalMixture (start - source) width kernel := by
  unfold intervalMixture
  refine Finset.sum_bij (fun point _ => point - source) ?_ ?_ ?_ ?_
  · intro point hpoint
    change point - source ∈ anchorInterval (start - source) width
    simp only [anchorInterval, Finset.mem_Ico] at *
    omega
  · intro first _ second _ heq
    change first - source = second - source at heq
    omega
  · intro point hpoint
    refine ⟨point + source, ?_, ?_⟩
    · simp only [anchorInterval, Finset.mem_Ico] at *
      omega
    · change point + source - source = point
      omega
  · intro point hpoint
    have hnew : point - source ∈ anchorInterval (start - source) width := by
      simp only [anchorInterval, Finset.mem_Ico] at *
      omega
    simp [intervalAnchorLaw, hpoint, hnew]

noncomputable def averagedLaw (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) : ℝ :=
  intervalMixture start width (fun shift => law modulus boundary (shift - source) color)

theorem averagedLaw_nonneg (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    0 ≤ averagedLaw modulus boundary start source width color := by
  unfold averagedLaw intervalMixture
  exact Finset.sum_nonneg fun shift _ => mul_nonneg (intervalAnchorLaw_nonneg _ _ _) (law_nonneg _ _ _ _)

/-- Uniform pointwise bound for the unshifted public slice mixture. -/
theorem averagedLaw_zero_le (modulus boundary start shiftBound : ℤ) (width : ℕ)
    (hwidth : width ≠ 0) (hbound : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hclearance : 2 * boundary + shiftBound < modulus) (color : ℤ) :
    averagedLaw modulus boundary start 0 width color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound) := by
  calc
    _ ≤ ∑ shift ∈ anchorInterval start width,
        intervalAnchorLaw start width shift * (1 / ((modulus : ℝ) - 2 * boundary - shiftBound)) := by
      unfold averagedLaw intervalMixture
      apply Finset.sum_le_sum
      intro shift hshift
      apply mul_le_mul_of_nonneg_left _ (intervalAnchorLaw_nonneg _ _ _)
      simpa only [Int.sub_zero] using law_le_of_shift_bound modulus boundary shift shiftBound color
        (hbound shift hshift) hclearance
    _ = _ := by rw [← Finset.sum_mul, intervalAnchorLaw_mass _ _ hwidth, one_mul]

/-- The source change has the exact V7 `cutoff/(width * remaining slice
length)` bound, derived from interval TV and the actual slice law. -/
theorem averagedLaw_source_variation (modulus boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (hwidth : width ≠ 0)
    (hbound : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff) (hclearance : 2 * boundary + shiftBound + cutoff < modulus)
    (color : ℤ) :
    |averagedLaw modulus boundary start source width color - averagedLaw modulus boundary start 0 width color| ≤
      (cutoff : ℝ) / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
  have hshiftBound (point : ℤ) (hpoint : point ∈ anchorInterval start width ∪ anchorInterval (start + -source) width) :
      |point| ≤ shiftBound + cutoff := by
    rcases Finset.mem_union.mp hpoint with hfirst | hsecond
    · have hs := hbound point hfirst
      have hc : 0 ≤ cutoff := (abs_nonneg source).trans hsource
      omega
    · have hbase : point + source ∈ anchorInterval start width := by
        simp only [anchorInterval, Finset.mem_Ico] at *
        omega
      have hb := hbound (point + source) hbase
      have hh := abs_sub (point + source) source
      simpa only [add_sub_cancel_right] using hh.trans (add_le_add hb hsource)
  have hden : 0 < (modulus : ℝ) - 2 * boundary - shiftBound - cutoff := by
    exact_mod_cast (show 0 < modulus - 2 * boundary - shiftBound - cutoff by omega)
  have hkernel (point : ℤ) (hpoint : point ∈ anchorInterval start width ∪ anchorInterval (start + -source) width) :
      0 ≤ law modulus boundary point color ∧ law modulus boundary point color ≤
        1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) := by
    refine ⟨law_nonneg _ _ _ _, ?_⟩
    have hh := law_le_of_shift_bound modulus boundary point (shiftBound + cutoff) color
      (hshiftBound point hpoint) (by omega)
    simpa only [Int.cast_add, sub_add_eq_sub_sub] using hh
  have hb := intervalMixture_shift_bound start (-source) width hwidth
    (fun point => law modulus boundary point color)
    (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) (by positivity) hkernel
  have hsourceReal : ((-source).natAbs : ℝ) ≤ cutoff := by
    rw [Int.natAbs_neg]
    have hh : ((source.natAbs : ℤ) : ℝ) ≤ (cutoff : ℝ) := by
      rw [Int.natCast_natAbs]
      exact_mod_cast hsource
    simpa only [Int.cast_natCast] using hh
  have hcut := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsourceReal (by positivity : 0 ≤ 1 /
      ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) (Nat.cast_nonneg width)
  have heq : averagedLaw modulus boundary start source width color =
      intervalMixture (start + -source) width (fun point => law modulus boundary point color) := by
    simpa only [averagedLaw, sub_eq_add_neg] using
      intervalMixture_translate start source width (fun point => law modulus boundary point color)
  calc
    _ = |intervalMixture (start + -source) width (fun point => law modulus boundary point color) -
        intervalMixture start width (fun point => law modulus boundary point color)| := by
      rw [heq]
      simp only [averagedLaw, Int.sub_zero]
    _ ≤ _ := hb.trans (hcut.trans_eq (by simp only [div_eq_mul_inv, mul_inv_rev]; ring))

/-- A finite source and public-blur mixture. A product index includes the
original source and independent public blur without altering either law. -/
noncomputable def mixedLaw {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ) : ℝ :=
  ∑ index, weights index * averagedLaw modulus boundary (starts index) (sources index) width color

theorem mixedLaw_nonneg {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ)
    (hweights : ∀ index, 0 ≤ weights index) :
    0 ≤ mixedLaw modulus boundary starts sources weights width color := by
  exact Finset.sum_nonneg fun index _ => mul_nonneg (hweights index) (averagedLaw_nonneg _ _ _ _ _ _)

/-- The actual unshifted slice average obeys the inverse deleted-length bound. -/
theorem mixedLaw_zero_le {τ : Type*} [Fintype τ] (modulus boundary shiftBound : ℤ)
    (starts : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (hwidth : width ≠ 0)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hclearance : 2 * boundary + shiftBound < modulus) (color : ℤ) :
    mixedLaw modulus boundary starts (fun _ => 0) weights width color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound) := by
  calc
    _ ≤ ∑ index, weights index * (1 / ((modulus : ℝ) - 2 * boundary - shiftBound)) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left
        (averagedLaw_zero_le modulus boundary (starts index) shiftBound width hwidth (hbound index)
          hclearance color) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

/-- Full source averaging preserves the sharp pointwise slice variation. -/
theorem mixedLaw_source_variation {τ : Type*} [Fintype τ] (modulus boundary shiftBound cutoff : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (hwidth : width ≠ 0)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) (color : ℤ) :
    |mixedLaw modulus boundary starts sources weights width color -
      mixedLaw modulus boundary starts (fun _ => 0) weights width color| ≤
      (cutoff : ℝ) / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
  unfold mixedLaw
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ index, |weights index * averagedLaw modulus boundary (starts index) (sources index) width color -
        weights index * averagedLaw modulus boundary (starts index) 0 width color| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ index, weights index * ((cutoff : ℝ) /
        ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) := by
      apply Finset.sum_le_sum
      intro index _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hweights index)]
      exact mul_le_mul_of_nonneg_left
        (averagedLaw_source_variation modulus boundary (starts index) (sources index) shiftBound cutoff width
          hwidth (hbound index) (hsources index) hclearance color) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

end AFT.TrimmedSlice

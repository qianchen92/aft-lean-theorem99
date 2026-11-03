import AFT.TrimmedSlice
import AFT.Charge

/-!
# Trimmed laws on the actual finite output palette
-/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- The actual slice, represented in the finite palette. -/
def paletteSlice (modulus : ℕ) (boundary shift : ℤ) : Finset (Fin modulus) :=
  Finset.univ.filter fun color => (color.val : ℤ) ∈ slice modulus boundary shift

theorem paletteSlice_image (modulus : ℕ) (boundary shift : ℤ) (hboundary : 0 ≤ boundary) :
    (paletteSlice modulus boundary shift).image (fun color => (color.val : ℤ)) =
      slice modulus boundary shift := by
  ext color
  constructor
  · intro hc
    obtain ⟨point, hp, rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp hp).2
  · intro hc
    have hb := (mem_slice modulus boundary shift color).mp hc
    have hcolor : 0 ≤ color ∧ color < modulus := by omega
    let point : Fin modulus := ⟨color.toNat, by omega⟩
    have heq : (point.val : ℤ) = color := by dsimp [point]; omega
    refine Finset.mem_image.mpr ⟨point, ?_, heq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ hc⟩

theorem paletteSlice_card (modulus : ℕ) (boundary shift : ℤ) (hboundary : 0 ≤ boundary) :
    (paletteSlice modulus boundary shift).card = ((modulus : ℤ) - 2 * boundary - |shift|).toNat := by
  have hinj : Function.Injective (fun color : Fin modulus => (color.val : ℤ)) := by
    intro first second heq
    apply Fin.ext
    dsimp only at heq
    exact_mod_cast heq
  have hh : ((paletteSlice modulus boundary shift).image (fun color => (color.val : ℤ))).card =
      (paletteSlice modulus boundary shift).card :=
    Finset.card_image_iff.mpr (Set.injOn_of_injective hinj)
  rw [paletteSlice_image modulus boundary shift hboundary, slice_card] at hh
  exact hh.symm

theorem paletteSlice_nonempty (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) :
    (paletteSlice modulus boundary shift).Nonempty := by
  apply Finset.card_pos.mp
  rw [paletteSlice_card modulus boundary shift hboundary]
  omega

/-- The uniform slice is a real finite probability distribution. -/
noncomputable def finiteLaw (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) : FiniteDist (Fin modulus) :=
  FiniteDist.uniformSafe (paletteSlice modulus boundary shift)
    (paletteSlice_nonempty modulus boundary shift hboundary hwidth)

theorem finiteLaw_weight (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) (color : Fin modulus) :
    (finiteLaw modulus boundary shift hboundary hwidth).weight color =
      law modulus boundary shift color.val := by
  simp only [finiteLaw, FiniteDist.uniformSafe, paletteSlice, Finset.mem_filter,
    Finset.mem_univ, true_and, law]
  rw [show (Finset.univ.filter fun color : Fin modulus => (color.val : ℤ) ∈ slice modulus boundary shift).card =
      (slice modulus boundary shift).card by
    rw [← paletteSlice, paletteSlice_card modulus boundary shift hboundary, slice_card]]

theorem law_palette_mass (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) :
    ∑ color : Fin modulus, law modulus boundary shift color.val = 1 := by
  simp_rw [← finiteLaw_weight modulus boundary shift hboundary hwidth]
  exact (finiteLaw modulus boundary shift hboundary hwidth).sum_one

/-- The finite uniform-on-subset L1 identity does not require a group structure. -/
theorem uniformSubset_l1 {ι : Type*} [Fintype ι] (subset : Finset ι) (hsubset : subset.Nonempty) :
    (∑ color, |(FiniteDist.uniformSafe subset hsubset).weight color - (Fintype.card ι : ℝ)⁻¹|) =
      2 * (1 - (subset.card : ℝ) / Fintype.card ι) := by
  classical
  have hs : (0 : ℝ) < subset.card := by exact_mod_cast hsubset.card_pos
  have hle : (subset.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ subset
  have hcard : (0 : ℝ) < Fintype.card ι := hs.trans_le hle
  have hi : (Fintype.card ι : ℝ)⁻¹ ≤ (subset.card : ℝ)⁻¹ := inv_anti₀ hs hle
  have hpoint (color : ι) :
      |(FiniteDist.uniformSafe subset hsubset).weight color - (Fintype.card ι : ℝ)⁻¹| =
        if color ∈ subset then (subset.card : ℝ)⁻¹ - (Fintype.card ι : ℝ)⁻¹
          else (Fintype.card ι : ℝ)⁻¹ := by
    by_cases hc : color ∈ subset
    · simp only [FiniteDist.uniformSafe, if_pos hc, abs_of_nonneg (sub_nonneg.mpr hi)]
    · simp [FiniteDist.uniformSafe, hc, abs_of_nonneg (inv_nonneg.mpr hcard.le)]
  simp_rw [hpoint]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcompl : (Finset.univ.filter fun color : ι => color ∉ subset).card = Fintype.card ι - subset.card := by
    simp [← Finset.sdiff_eq_filter, Finset.card_sdiff]
  rw [hcompl, Nat.cast_sub (Finset.card_le_univ subset)]
  field_simp
  ring

/-- Exact L1 deviation of the real trimmed slice from palette uniformity. -/
theorem law_palette_l1 (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) :
    (∑ color : Fin modulus, |law modulus boundary shift color.val - (modulus : ℝ)⁻¹|) =
      2 * (2 * (boundary : ℝ) + |(shift : ℝ)|) / modulus := by
  have hcard : ((paletteSlice modulus boundary shift).card : ℤ) =
      (modulus : ℤ) - 2 * boundary - |shift| := by
    rw [paletteSlice_card modulus boundary shift hboundary, Int.toNat_of_nonneg (by omega)]
  have hcardReal : ((paletteSlice modulus boundary shift).card : ℝ) =
      (modulus : ℝ) - 2 * boundary - |(shift : ℝ)| := by exact_mod_cast hcard
  have hmodulus : (modulus : ℝ) ≠ 0 := by
    have hnonneg := abs_nonneg shift
    have hh : 0 < modulus := by omega
    exact_mod_cast (ne_of_gt hh)
  simp_rw [← finiteLaw_weight modulus boundary shift hboundary hwidth]
  change (∑ color : Fin modulus, |(FiniteDist.uniformSafe _ _).weight color - _|) = _
  rw [show (modulus : ℝ)⁻¹ = (Fintype.card (Fin modulus) : ℝ)⁻¹ by simp,
    uniformSubset_l1, Fintype.card_fin, hcardReal]
  field_simp
  ring

/-- Actual source displacement and trimming yield a uniform finite-palette
L1 bound for each public interval mixture. -/
theorem averagedLaw_palette_l1_le (modulus : ℕ) (boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (hwidth : width ≠ 0) (hboundary : 0 ≤ boundary)
    (hbound : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff) (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    (∑ color : Fin modulus, |averagedLaw modulus boundary start source width color.val - (modulus : ℝ)⁻¹|) ≤
      2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus := by
  have hshift (shift : ℤ) (hs : shift ∈ anchorInterval start width) :
      |shift - source| ≤ shiftBound + cutoff := (abs_sub _ _).trans (add_le_add (hbound shift hs) hsource)
  have hmass := intervalAnchorLaw_mass start width hwidth
  have hrepr (color : Fin modulus) : averagedLaw modulus boundary start source width color.val - (modulus : ℝ)⁻¹ =
      ∑ shift ∈ anchorInterval start width,
        intervalAnchorLaw start width shift * (law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹) := by
    simp only [averagedLaw, intervalMixture, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
  calc
    _ ≤ ∑ color : Fin modulus, ∑ shift ∈ anchorInterval start width,
        intervalAnchorLaw start width shift * |law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹| := by
      apply Finset.sum_le_sum
      intro color _
      rw [hrepr]
      simpa only [abs_mul, abs_of_nonneg (intervalAnchorLaw_nonneg _ _ _)] using Finset.abs_sum_le_sum_abs
        (fun shift => intervalAnchorLaw start width shift * (law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹))
        (anchorInterval start width)
    _ = ∑ shift ∈ anchorInterval start width, intervalAnchorLaw start width shift *
        ∑ color : Fin modulus, |law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ shift ∈ anchorInterval start width, intervalAnchorLaw start width shift *
        (2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus) := by
      apply Finset.sum_le_sum
      intro shift hs
      apply mul_le_mul_of_nonneg_left _ (intervalAnchorLaw_nonneg _ _ _)
      rw [law_palette_l1 modulus boundary (shift - source) hboundary (by have := hshift shift hs; omega)]
      have hh : |((shift - source : ℤ) : ℝ)| ≤ (shiftBound : ℝ) + cutoff := by exact_mod_cast hshift shift hs
      exact div_le_div_of_nonneg_right (by push_cast at hh ⊢; linarith) (Nat.cast_nonneg modulus)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem averagedLaw_palette_mass (modulus : ℕ) (boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (hwidth : width ≠ 0) (hboundary : 0 ≤ boundary)
    (hbound : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff) (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ color : Fin modulus, averagedLaw modulus boundary start source width color.val = 1 := by
  unfold averagedLaw intervalMixture
  rw [Finset.sum_comm]
  have heq (shift : ℤ) (hs : shift ∈ anchorInterval start width) :
      (∑ color : Fin modulus, intervalAnchorLaw start width shift * law modulus boundary (shift - source) color.val) =
        intervalAnchorLaw start width shift := by
    rw [← Finset.mul_sum, law_palette_mass modulus boundary (shift - source) hboundary, mul_one]
    have hh := (abs_sub shift source).trans (add_le_add (hbound shift hs) hsource)
    omega
  simpa only [Finset.sum_congr rfl heq] using intervalAnchorLaw_mass start width hwidth

theorem mixedLaw_palette_mass {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (hmass : ∑ index, weights index = 1)
    (hboundary : 0 ≤ boundary)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ color : Fin modulus, mixedLaw modulus boundary starts sources weights width color.val = 1 := by
  unfold mixedLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, averagedLaw_palette_mass modulus boundary _ _ shiftBound cutoff width hwidth
    hboundary (hbound _) (hsources _) hclearance, mul_one]
  exact hmass

theorem mixedLaw_palette_l1_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hboundary : 0 ≤ boundary)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    (∑ color : Fin modulus, |mixedLaw modulus boundary starts sources weights width color.val - (modulus : ℝ)⁻¹|) ≤
      2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus := by
  have hrepr (color : Fin modulus) : mixedLaw modulus boundary starts sources weights width color.val - (modulus : ℝ)⁻¹ =
      ∑ index, weights index * (averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹) := by
    simp only [mixedLaw, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
  calc
    _ ≤ ∑ color : Fin modulus, ∑ index, weights index *
        |averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹| := by
      apply Finset.sum_le_sum
      intro color _
      rw [hrepr]
      simpa only [abs_mul, abs_of_nonneg (hweights _)] using Finset.abs_sum_le_sum_abs
        (fun index => weights index * (averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹))
        Finset.univ
    _ = ∑ index, weights index * ∑ color : Fin modulus,
        |averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ index, weights index * (2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left
        (averagedLaw_palette_l1_le modulus boundary (starts index) (sources index) shiftBound cutoff width hwidth
          hboundary (hbound index) (hsources index) hclearance) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem mixedLaw_zero_boundary {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ)
    (hout : color < boundary ∨ modulus - 1 - boundary < color) :
    mixedLaw modulus boundary starts sources weights width color = 0 := by
  unfold mixedLaw averagedLaw intervalMixture
  simp only [law_zero_outside _ _ _ _ hout, mul_zero, Finset.sum_const_zero]

/-- The source-averaged mixture retains the trimmed-slice supremum bound. -/
theorem mixedLaw_le {τ : Type*} [Fintype τ] (modulus boundary shiftBound cutoff : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (hwidth : width ≠ 0)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) (color : ℤ) :
    mixedLaw modulus boundary starts sources weights width color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) := by
  have hlocal (index : τ) : averagedLaw modulus boundary (starts index) (sources index) width color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) := by
    unfold averagedLaw intervalMixture
    calc
      _ ≤ ∑ shift ∈ anchorInterval (starts index) width, intervalAnchorLaw (starts index) width shift *
          (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
        apply Finset.sum_le_sum
        intro shift hs
        apply mul_le_mul_of_nonneg_left _ (intervalAnchorLaw_nonneg _ _ _)
        have hh := law_le_of_shift_bound modulus boundary (shift - sources index) (shiftBound + cutoff) color
          ((abs_sub _ _).trans (add_le_add (hbound index shift hs) (hsources index))) (by omega)
        simpa only [Int.cast_add, sub_add_eq_sub_sub] using hh
      _ = _ := by rw [← Finset.sum_mul, intervalAnchorLaw_mass _ _ hwidth, one_mul]
  calc
    _ ≤ ∑ index, weights index * (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hlocal index) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

end AFT.TrimmedSlice

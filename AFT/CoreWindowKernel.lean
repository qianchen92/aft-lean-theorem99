import AFT.MaskedWindowTranslation
import AFT.SafePairCore

/-! # Identification of the actual restricted pair with its integer core kernel -/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- The core mask is the original integer palette interval, not a cyclic
window or a replacement endpoint law. -/
theorem core_interval_mem (modulus coreDepth : ℕ) (hcore : 2 * coreDepth ≤ modulus) (color : ℤ) :
    color ∈ anchorInterval coreDepth (modulus - 2 * coreDepth) ↔
      (coreDepth : ℤ) ≤ color ∧ color < (modulus : ℤ) - coreDepth := by
  simp only [anchorInterval, Finset.mem_Ico]
  omega

theorem core_palette_mem (modulus coreDepth : ℕ) (color : Fin modulus) :
    color ∈ paletteSlice modulus coreDepth 0 ↔
      (coreDepth : ℤ) ≤ color.val ∧ (color.val : ℤ) < (modulus : ℤ) - coreDepth := by
  simp only [paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and, slice,
    max_self, min_self, add_zero, Finset.mem_Ico]

/-- Exact equality between the actual core-restricted window pair and the
integer kernel to which the complete translation bound applies. -/
theorem restricted_averagedPair_eq_maskedIntegerPair (modulus coreDepth : ℕ)
    (boundary start source shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ modulus) (hboundary : boundary ≤ coreDepth)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound) (hsource : |source| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff)
    (first second : Fin modulus) :
    SafePair.restrictPair (paletteSlice modulus coreDepth 0) (averagedPair modulus boundary start source width) first second =
      maskedIntegerPair modulus boundary lower start source width coreDepth (modulus - 2 * coreDepth) first.val second.val := by
  have hfloor : ⌊(modulus : ℝ) - 1⌋ = (modulus : ℤ) - 1 := by
    have heq : (modulus : ℝ) - 1 = ((modulus : ℤ) - 1 : ℤ) := by push_cast; rfl
    rw [heq, Int.floor_intCast]
  unfold SafePair.restrictPair maskedIntegerPair
  simp only [core_palette_mem, core_interval_mem modulus coreDepth hcore, hfloor]
  split_ifs with hc
  · rw [averagedPair_eq_weightedIntegerWindow modulus boundary start source shiftBound cutoff width lower hlower
      hstarts hsource hclear]
    have hmask : boundary ≤ (first.val : ℤ) ∧ (first.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
        boundary ≤ (second.val : ℤ) ∧ (second.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary := by omega
    rw [if_pos hmask]
  · rfl

end AFT.TrimmedSlice

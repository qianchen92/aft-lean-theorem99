import AFT.PairCoreNumerics

/-! # Complete energy bounds for the true core-supported integer pair -/

namespace AFT.TrimmedSlice

open scoped BigOperators
open SafeConvolution

variable {τ : Type*} [Fintype τ]

/-- The three nonsmoothing costs follow from the actual pair law,
its exact marginal, and its interval-trimming denominator. -/
theorem mixedPair_core_bounds
    (modulus : ℕ) (boundary shiftBound cutoff coreDepth : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hcore : 0 ≤ coreDepth) (hcoreSmall : 2 * coreDepth < modulus)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    let denominator := (modulus : ℝ) - 2 * boundary - shiftBound - cutoff
    let mass := mixedPair modulus boundary starts sources sourceLaw.weight width
    let core := paletteSlice modulus coreDepth 0
    let seed := fun color : Fin modulus × Fin modulus => SafePair.coreSeed core mass color.1 color.2
    countingL2 seed ≤ Real.sqrt (1 / ((width : ℝ) * denominator)) ∧
    SafePair.pairCountingL2 (SafePair.coreSeed core mass - SafePair.canonicalPair (fun _ => 1 / (modulus : ℝ))
      (SafePair.restrictPair core mass)) ≤
      Real.sqrt (1 / (core.card : ℝ) - 1 / (modulus : ℝ)) *
        (2 * Real.sqrt (1 / denominator) + Real.sqrt (1 / (core.card : ℝ)) + Real.sqrt (1 / (modulus : ℝ))) ∧
    countingL2 (fun color : Fin modulus × Fin modulus => SafePair.restrictPair core mass color.1 color.2 - mass color.1 color.2) ≤
      Real.sqrt (4 * (coreDepth : ℝ) / ((width : ℝ) * denominator ^ 2)) := by
  dsimp only
  let denominator := (modulus : ℝ) - 2 * boundary - shiftBound - cutoff
  let mass := mixedPair modulus boundary starts sources sourceLaw.weight width
  let core := paletteSlice modulus coreDepth 0
  have hd : 0 < denominator := by
    dsimp only [denominator]
    have hh : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - shiftBound - cutoff := by omega
    exact_mod_cast hh
  have hnonneg := mixedPair_nonneg modulus boundary starts sources sourceLaw.weight width sourceLaw.nonneg
  have hmass := mixedPair_mass modulus boundary shiftBound cutoff width hwidth starts sources sourceLaw.weight
    sourceLaw.sum_one hb hstarts hsources hclear
  have hheight := mixedPair_le modulus boundary shiftBound cutoff width starts sources sourceLaw.weight
    sourceLaw.nonneg sourceLaw.sum_one hstarts hsources hclear
  have hrow (first : Fin modulus) : (∑ second, mass first second) ≤ 1 / denominator := by
    dsimp only [mass]
    rw [mixedPair_first_marginal _ _ _ _ _ _ hb]
    simpa only [Int.cast_natCast] using mixedLaw_le (modulus : ℤ) boundary shiftBound cutoff starts sources
      sourceLaw.weight width hwidth sourceLaw.nonneg sourceLaw.sum_one hstarts hsources hclear first.val
  have hcolumn (second : Fin modulus) : (∑ first, mass first second) ≤ 1 / denominator := by
    simpa only [mass, mixedPair_symmetric modulus boundary starts sources sourceLaw.weight width _ second] using hrow second
  have hne : core.Nonempty := by
    apply Finset.card_pos.mp
    dsimp only [core]
    rw [paletteSlice_card _ _ _ hcore]
    simp only [abs_zero, sub_zero]
    omega
  constructor
  · apply Real.sqrt_le_sqrt
    calc
      _ = ∑ first, ∑ second, SafePair.coreSeed core mass first second ^ 2 := Fintype.sum_prod_type _
      _ ≤ ∑ first, ∑ second, mass first second ^ 2 := SafePair.coreSeed_square_le core mass hne
      _ ≤ ∑ first, ∑ second, (1 / ((width : ℝ) * denominator)) * mass first second := by
        apply Finset.sum_le_sum
        intro first _
        apply Finset.sum_le_sum
        intro second _
        have hh := mul_le_mul_of_nonneg_right (hheight first second) (hnonneg first second)
        nlinarith only [hh]
      _ = _ := by simp only [← Finset.mul_sum, mass, hmass, mul_one]; rfl
  constructor
  · simpa only [Fintype.card_fin] using SafePair.coreSeed_reference_error_le core hne mass
      (1 / denominator) (by positivity) hnonneg hmass.le hrow hcolumn
  · apply Real.sqrt_le_sqrt
    have hh := SafePair.actual_core_square_loss modulus boundary shiftBound cutoff coreDepth width hwidth
      starts sources sourceLaw hb hcore hcoreSmall.le hstarts hsources hclear
    simpa only [Fintype.sum_prod_type, show ∀ a b : ℝ, (a - b) ^ 2 = (b - a) ^ 2 by intro a b; ring] using hh

end AFT.TrimmedSlice

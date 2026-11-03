import AFT.TrimmedPair
import AFT.V7PrimaryCalibration

/-!
# Safely supported canonical seeds for the true integer-window pair
-/

namespace AFT.SafePair

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def restrictPair (core : Finset ι) (mass : ι → ι → ℝ) (first second : ι) : ℝ :=
  if first ∈ core ∧ second ∈ core then mass first second else 0

/-- Canonicalize the actual signed pair by subtracting both true marginals
and restoring its total mass once. -/
noncomputable def canonicalPair (reference : ι → ℝ) (mass : ι → ι → ℝ) (first second : ι) : ℝ :=
  mass first second - reference first * (∑ x, mass x second) -
    (∑ y, mass first y) * reference second +
    (∑ x, ∑ y, mass x y) * reference first * reference second

omit [DecidableEq ι] in
theorem canonicalPair_first (reference : ι → ℝ) (mass : ι → ι → ℝ)
    (href : ∑ color, reference color = 1) (first : ι) :
    ∑ second, canonicalPair reference mass first second = 0 := by
  unfold canonicalPair
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, href, mul_one]
  rw [Finset.sum_comm (f := fun y x => mass x y)]
  ring

omit [DecidableEq ι] in
theorem canonicalPair_transpose (reference : ι → ℝ) (mass : ι → ι → ℝ) (first second : ι) :
    canonicalPair reference mass first second =
      canonicalPair reference (fun x y => mass y x) second first := by
  unfold canonicalPair
  rw [Finset.sum_comm (f := fun x y => mass y x)]
  ring

omit [DecidableEq ι] in
theorem canonicalPair_second (reference : ι → ℝ) (mass : ι → ι → ℝ)
    (href : ∑ color, reference color = 1) (second : ι) :
    ∑ first, canonicalPair reference mass first second = 0 := by
  simp_rw [canonicalPair_transpose reference mass]
  exact canonicalPair_first reference (fun x y => mass y x) href second

/-- The actual seed obtained by deleting the edge strips and using uniform
core centering. Its mass and both marginals are exactly zero. -/
noncomputable def coreSeed (core : Finset ι) (mass : ι → ι → ℝ) : ι → ι → ℝ :=
  canonicalPair (uniformFiniteProfile core) (restrictPair core mass)

theorem coreSeed_canonical (core : Finset ι) (mass : ι → ι → ℝ) (hne : core.Nonempty) :
    (∀ first, ∑ second, coreSeed core mass first second = 0) ∧
    (∀ second, ∑ first, coreSeed core mass first second = 0) :=
  ⟨canonicalPair_first _ _ (uniformFiniteProfile_mass core hne),
    canonicalPair_second _ _ (uniformFiniteProfile_mass core hne)⟩

theorem coreSeed_supported (core : Finset ι) (mass : ι → ι → ℝ)
    (first second : ι) (hout : first ∉ core ∨ second ∉ core) :
    coreSeed core mass first second = 0 := by
  rcases hout with hfirst | hsecond
  · simp [coreSeed, canonicalPair, uniformFiniteProfile, restrictPair, hfirst]
  · simp [coreSeed, canonicalPair, uniformFiniteProfile, restrictPair, hsecond]

/-- Deleting either edge strip is charged to its actual fixed-coordinate
square sum. There is no ambient-palette union bound. -/
theorem restriction_square_loss (core : Finset ι) (mass : ι → ι → ℝ) (rowBound : ℝ)
    (hrow : ∀ first, (∑ second, mass first second ^ 2) ≤ rowBound)
    (hcolumn : ∀ second, (∑ first, mass first second ^ 2) ≤ rowBound) :
    (∑ first, ∑ second, (mass first second - restrictPair core mass first second) ^ 2) ≤
      2 * (coreᶜ.card : ℝ) * rowBound := by
  have hfilter : (Finset.univ.filter fun color : ι => color ∉ core) = coreᶜ := by ext; simp
  have hfirst : (∑ first : ι, ∑ second : ι, if first ∉ core then mass first second ^ 2 else 0) ≤
      (coreᶜ.card : ℝ) * rowBound := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite, hfilter]
    simp only [Finset.sum_const_zero, add_zero]
    calc
      _ ≤ ∑ _first ∈ coreᶜ, rowBound := Finset.sum_le_sum fun first _ => hrow first
      _ = _ := by simp
  have hsecond : (∑ first : ι, ∑ second : ι, if second ∉ core then mass first second ^ 2 else 0) ≤
      (coreᶜ.card : ℝ) * rowBound := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite, hfilter]
    simp only [Finset.sum_const_zero, add_zero]
    calc
      _ ≤ ∑ _second ∈ coreᶜ, rowBound := Finset.sum_le_sum fun second _ => hcolumn second
      _ = _ := by simp
  calc
    _ ≤ ∑ first, ∑ second, ((if first ∉ core then mass first second ^ 2 else 0) +
        (if second ∉ core then mass first second ^ 2 else 0)) := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      by_cases hf : first ∈ core <;> by_cases hs : second ∈ core <;>
        simp [restrictPair, hf, hs, sq_nonneg]
    _ = (∑ first, ∑ second, if first ∉ core then mass first second ^ 2 else 0) +
        (∑ first, ∑ second, if second ∉ core then mass first second ^ 2 else 0) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith

/-- For the actual integer-window pair, the deleted-core square loss is
`4*coreDepth/(W*(q-D)^2)` before uniform-profile scaling by q². -/
theorem actual_core_square_loss {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff coreDepth : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hcore : 0 ≤ coreDepth) (hcoreSmall : 2 * coreDepth ≤ modulus)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    let mass := TrimmedSlice.mixedPair modulus boundary starts sources sourceLaw.weight width
    let core := TrimmedSlice.paletteSlice modulus coreDepth 0
    (∑ first, ∑ second, (mass first second - restrictPair core mass first second) ^ 2) ≤
      4 * (coreDepth : ℝ) /
        ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2) := by
  dsimp only
  have hrow := TrimmedSlice.mixedPair_fiber_square_le modulus boundary shiftBound cutoff width hwidth
    starts sources sourceLaw hb hstarts hsources hclear
  have hcolumn (second : Fin modulus) :
      (∑ first, TrimmedSlice.mixedPair modulus boundary starts sources sourceLaw.weight width first second ^ 2) ≤
        1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2) := by
    simpa only [TrimmedSlice.mixedPair_symmetric modulus boundary starts sources sourceLaw.weight width _ second] using hrow second
  have hcard : ((TrimmedSlice.paletteSlice modulus coreDepth 0)ᶜ.card : ℝ) = 2 * (coreDepth : ℝ) := by
    exact_mod_cast boundaryPalette_card modulus coreDepth hcore hcoreSmall
  have hh := restriction_square_loss (TrimmedSlice.paletteSlice modulus coreDepth 0)
    (TrimmedSlice.mixedPair modulus boundary starts sources sourceLaw.weight width)
    (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2)) hrow hcolumn
  rw [hcard] at hh
  exact hh.trans_eq (by ring)

end AFT.SafePair

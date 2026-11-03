import AFT.V7PrimaryInverse

/-!
# Reflection symmetry of the actual calibrated primary law
-/

namespace AFT

open scoped BigOperators

namespace TrimmedSlice

def reflectedStart (start : ℤ) (width : ℕ) : ℤ := -start - width + 1

theorem law_reflection (modulus boundary shift color : ℤ) :
    law modulus boundary shift (modulus - 1 - color) = law modulus boundary (-shift) color := by
  have hm : modulus - 1 - color ∈ slice modulus boundary shift ↔ color ∈ slice modulus boundary (-shift) := by
    simp only [mem_slice]
    omega
  simp only [law, hm, slice_card, abs_neg]

theorem intervalAnchorLaw_reflection (start color : ℤ) (width : ℕ) :
    intervalAnchorLaw (reflectedStart start width) width (-color) = intervalAnchorLaw start width color := by
  have hm : -color ∈ anchorInterval (reflectedStart start width) width ↔ color ∈ anchorInterval start width := by
    simp only [anchorInterval, Finset.mem_Ico, reflectedStart]
    omega
  simp only [intervalAnchorLaw, hm]

theorem averagedLaw_reflection (modulus boundary start source color : ℤ) (width : ℕ) :
    averagedLaw modulus boundary start source width (modulus - 1 - color) =
      averagedLaw modulus boundary (reflectedStart start width) (-source) width color := by
  unfold averagedLaw intervalMixture
  apply Finset.sum_bij (fun offset _ => -offset)
  · intro offset ho
    simp only [anchorInterval, Finset.mem_Ico, reflectedStart] at ho ⊢
    omega
  · intro a _ b _ hab
    omega
  · intro offset ho
    refine ⟨-offset, ?_, by omega⟩
    simp only [anchorInterval, Finset.mem_Ico, reflectedStart] at ho ⊢
    omega
  · intro offset _
    dsimp only
    rw [intervalAnchorLaw_reflection, law_reflection]
    congr 2
    ring

/-- Reflection uses an actual measure-preserving sign reversal of the
original source state, so no independent source copy is introduced. -/
theorem mixedLaw_reflection {τ : Type*} [Fintype τ]
    (modulus boundary : ℤ) (width : ℕ) (starts targets sources : τ → ℤ) (weights : τ → ℝ)
    (reverse : τ ≃ τ) (hw : ∀ index, weights (reverse index) = weights index)
    (hs : ∀ index, sources (reverse index) = -sources index)
    (ha : ∀ index, targets (reverse index) = reflectedStart (starts index) width) (color : ℤ) :
    mixedLaw modulus boundary starts sources weights width (modulus - 1 - color) =
      mixedLaw modulus boundary targets sources weights width color := by
  unfold mixedLaw
  calc
    _ = ∑ index, weights (reverse index) * averagedLaw modulus boundary
        (targets (reverse index)) (sources (reverse index)) width color := by
      apply Finset.sum_congr rfl
      intro index _
      rw [hw, ha, hs, averagedLaw_reflection]
    _ = _ := Equiv.sum_comp reverse (fun index => weights index *
      averagedLaw modulus boundary (targets index) (sources index) width color)

theorem fairMixedLaw_reflection {τ : Type*} [Fintype τ]
    (modulus boundary : ℤ) (width : ℕ) (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ)
    (reverse : τ ≃ τ) (hw : ∀ index, weights (reverse index) = weights index)
    (hs : ∀ index, sources (reverse index) = -sources index)
    (hplus : ∀ index, startsPlus (reverse index) = reflectedStart (startsMinus index) width)
    (hminus : ∀ index, startsMinus (reverse index) = reflectedStart (startsPlus index) width) (color : ℤ) :
    fairMixedLaw modulus boundary startsPlus startsMinus sources weights width (modulus - 1 - color) =
      fairMixedLaw modulus boundary startsPlus startsMinus sources weights width color := by
  unfold fairMixedLaw
  rw [mixedLaw_reflection modulus boundary width startsPlus startsMinus sources weights reverse hw hs hminus,
    mixedLaw_reflection modulus boundary width startsMinus startsPlus sources weights reverse hw hs hplus]
  ring

theorem blurredSafeLaw_reflection {σ : Type*} [Fintype σ]
    (modulus margin : ℤ) (shifts : σ → ℤ) (weights : σ → ℝ)
    (reverse : σ ≃ σ) (hw : ∀ index, weights (reverse index) = weights index)
    (hs : ∀ index, shifts (reverse index) = -shifts index)
    (hwidth : 2 * margin ≤ modulus) (color : ℤ) :
    blurredSafeLaw modulus margin shifts weights (modulus - 1 - color) =
      blurredSafeLaw modulus margin shifts weights color := by
  have hcast : ((modulus - 2 * margin).toNat : ℤ) = modulus - 2 * margin := Int.toNat_of_nonneg (by omega)
  have hrow (shift : ℤ) : intervalAnchorLaw margin (modulus - 2 * margin).toNat (modulus - 1 - color - shift) =
      intervalAnchorLaw margin (modulus - 2 * margin).toNat (color - -shift) := by
    have hm : modulus - 1 - color - shift ∈ anchorInterval margin (modulus - 2 * margin).toNat ↔
        color - -shift ∈ anchorInterval margin (modulus - 2 * margin).toNat := by
      simp only [anchorInterval, Finset.mem_Ico, hcast]
      omega
    simp only [intervalAnchorLaw, hm]
  unfold blurredSafeLaw
  calc
    _ = ∑ index, weights (reverse index) * intervalAnchorLaw margin (modulus - 2 * margin).toNat
        (color - shifts (reverse index)) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [hw, hs, hrow]
    _ = _ := Equiv.sum_comp reverse (fun index => weights index *
      intervalAnchorLaw margin (modulus - 2 * margin).toNat (color - shifts index))

end TrimmedSlice

namespace V7Calibration

theorem palette_rev_val (modulus : ℕ) (color : Fin modulus) :
    (color.rev.val : ℤ) = (modulus : ℤ) - 1 - color.val := by
  simp only [Fin.val_rev]
  omega

theorem paletteSign_rev (modulus : ℕ) (color : Fin modulus) :
    paletteSign modulus color.rev = -paletteSign modulus color := by
  unfold paletteSign
  simp only [Fin.val_rev]
  split_ifs <;> norm_num <;> omega

theorem boundaryPalette_rev (modulus : ℕ) (boundary : ℤ) (color : Fin modulus) :
    color.rev ∈ boundaryPalette modulus boundary ↔ color ∈ boundaryPalette modulus boundary := by
  simp only [mem_boundaryPalette, palette_rev_val]
  omega

/-- Reflected source laws imply reflection symmetry of the computed base
primary, rather than requiring that symmetry as a probability hypothesis. -/
theorem basePrimary_reflection {σ τ : Type*} [Fintype σ] [Fintype τ]
    (parameter : ℕ) (cutoffScale : ℝ) (boundary : ℤ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ)
    (bodyReverse : σ ≃ σ) (sourceReverse : τ ≃ τ)
    (hbw : ∀ index, bodyLaw.weight (bodyReverse index) = bodyLaw.weight index)
    (hbs : ∀ index, bodyShifts (bodyReverse index) = -bodyShifts index)
    (hsw : ∀ index, sourceLaw.weight (sourceReverse index) = sourceLaw.weight index)
    (hss : ∀ index, sources (sourceReverse index) = -sources index)
    (hplus : ∀ index, startsPlus (sourceReverse index) = TrimmedSlice.reflectedStart (startsMinus index) (Parameters.anchorWidth parameter))
    (hminus : ∀ index, startsMinus (sourceReverse index) = TrimmedSlice.reflectedStart (startsPlus index) (Parameters.anchorWidth parameter))
    (hwidth : 2 * (Parameters.safeMargin parameter : ℤ) ≤ Parameters.modulus parameter)
    (color : Fin (Parameters.modulus parameter)) :
    basePrimary parameter cutoffScale boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw color.rev =
      basePrimary parameter cutoffScale boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw color := by
  unfold basePrimary TrimmedSlice.actualFairBasePrimary basePrimaryProfile
  rw [palette_rev_val,
    TrimmedSlice.blurredSafeLaw_reflection _ _ _ _ bodyReverse hbw hbs hwidth,
    TrimmedSlice.fairMixedLaw_reflection _ _ _ _ _ _ _ sourceReverse hsw hss hplus hminus,
    TrimmedSlice.fairMixedLaw_reflection _ _ _ _ _ _ _ sourceReverse hsw (by simp) hplus hminus]

/-- The beta repair is reflection symmetric because both actual palette
pieces are reflection invariant. -/
theorem primary_reflection {σ τ : Type*} [Fintype σ] [Fintype τ]
    (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ)
    (hbase : ∀ color, basePrimary parameter cutoffScale boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw color.rev =
      basePrimary parameter cutoffScale boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw color)
    (color : Fin (Parameters.modulus parameter)) :
    primary parameter cutoffScale beta boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw color.rev =
      primary parameter cutoffScale beta boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw color := by
  simp only [primary, calibratedPrimaryProfile, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, uniformFiniteProfile, Finset.mem_compl, boundaryPalette_rev, hbase]

/-- The actual primary sign has mean zero under any reflected primary;
this is the exact fairness identity needed for the sign-mixture model. -/
theorem paletteSign_mean_zero (modulus : ℕ) (primaryLaw : Fin modulus → ℝ)
    (hsym : ∀ color, primaryLaw color.rev = primaryLaw color) :
    ∑ color, primaryLaw color * paletteSign modulus color = 0 := by
  have hh := Equiv.sum_comp (Fin.revPerm : Fin modulus ≃ Fin modulus)
    (fun color => primaryLaw color * paletteSign modulus color)
  change (∑ color : Fin modulus, primaryLaw color.rev * paletteSign modulus color.rev) = _ at hh
  simp only [hsym, paletteSign_rev, mul_neg, Finset.sum_neg_distrib] at hh
  linarith

end V7Calibration
end AFT

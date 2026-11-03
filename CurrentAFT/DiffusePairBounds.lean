import CurrentAFT.DiffusePair
import CurrentAFT.BackgroundLinear

/-!
# Concrete current-parameter quadratic diffuse-pair budgets

The body density is obtained from the actual safe pair seed and the proved
positive safe reference. The smoothing estimate is the complete estimate
for the original integer slice, evaluated at the actual `q,A,B` family.
-/

namespace CurrentAFT.DiffusePairBounds

open AFT AFT.TrimmedSlice AFT.SafeConvolution DiffuseProfiles ProposalPrimary
  ActualControls FirstResponse PairSmoothing DiffusePair BackgroundRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  DiffusePair.pairProfile DiffusePair.safePairProfile DiffusePair.liftedPairProfile
  DiffusePair.rootPairLaw DiffusePair.rootPairShift

theorem safe_sum_eq (security : ℕ) (profile : ActualControls.Palette security → ℝ)
    (hzero : ∀ color, ¬InwardAnchor.SafeColor security color → profile color = 0) :
    (∑ color : SafePalette security, profile color.val) = ∑ color, profile color := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (InwardAnchor.SafeColor security) profile
  have houtside : (∑ color : {color // ¬InwardAnchor.SafeColor security color}, profile color.val) = 0 := by
    apply Finset.sum_eq_zero
    intro color _
    exact hzero color.val color.property
  rw [houtside, add_zero] at hsplit
  exact hsplit

def bodyPairDensity (security : ℕ) (scalar : ℤ) (first second : SafePalette security) : ℝ :=
  safePairProfile security scalar first.val second.val /
    ((bodyReference security).weight first * (bodyReference security).weight second)

theorem safePairProfile_symmetric (security : ℕ) (scalar : ℤ)
    (first second : ActualControls.Palette security) :
    safePairProfile security scalar first second = safePairProfile security scalar second first := by
  have htranspose : (fun first second =>
      AFT.SafePair.restrictPair (safeCore security) (pairProfile security scalar) second first) =
      AFT.SafePair.restrictPair (safeCore security) (pairProfile security scalar) := by
    funext first second
    by_cases hfirst : first ∈ safeCore security <;> by_cases hsecond : second ∈ safeCore security <;>
      simp only [AFT.SafePair.restrictPair, hfirst, hsecond, and_self, and_true, and_false,
        if_true, if_false, pairProfile_symmetric security scalar]
  unfold safePairProfile AFT.SafePair.coreSeed
  rw [AFT.SafePair.canonicalPair_transpose, htranspose]

theorem bodyPairDensity_symmetric (security : ℕ) (scalar : ℤ) (first second : SafePalette security) :
    bodyPairDensity security scalar first second = bodyPairDensity security scalar second first := by
  rw [bodyPairDensity, bodyPairDensity, safePairProfile_symmetric, mul_comm]

theorem bodyPairDensity_profile (security : ℕ) (scalar : ℤ) (first second : SafePalette security) :
    (bodyReference security).weight first * (bodyReference security).weight second *
      bodyPairDensity security scalar first second = safePairProfile security scalar first.val second.val := by
  unfold bodyPairDensity
  exact mul_div_cancel₀ _ (mul_ne_zero (bodyReference_positive security first).ne'
    (bodyReference_positive security second).ne')

theorem bodyPairDensity_centered_second (security : ℕ) (scalar : ℤ) (first : SafePalette security) :
    (∑ second, (bodyReference security).weight second * bodyPairDensity security scalar first second) = 0 := by
  have hpoint (second : SafePalette security) :
      (bodyReference security).weight second * bodyPairDensity security scalar first second =
        safePairProfile security scalar first.val second.val / (bodyReference security).weight first := by
    unfold bodyPairDensity
    field_simp [(bodyReference_positive security first).ne', (bodyReference_positive security second).ne']
  simp only [hpoint, ← Finset.sum_div]
  rw [safe_sum_eq security _ (fun color hunsafe => safePairProfile_zero_outside security scalar first.val color (Or.inr hunsafe)),
    (safePairProfile_canonical security scalar).1, zero_div]

theorem bodyPairDensity_centered_first (security : ℕ) (scalar : ℤ) (second : SafePalette security) :
    (∑ first, (bodyReference security).weight first * bodyPairDensity security scalar first second) = 0 := by
  have hpoint (first : SafePalette security) :
      (bodyReference security).weight first * bodyPairDensity security scalar first second =
        safePairProfile security scalar first.val second.val / (bodyReference security).weight second := by
    unfold bodyPairDensity
    field_simp [(bodyReference_positive security first).ne', (bodyReference_positive security second).ne']
  simp only [hpoint, ← Finset.sum_div]
  rw [safe_sum_eq security _ (fun color hunsafe => safePairProfile_zero_outside security scalar color second.val (Or.inl hunsafe)),
    (safePairProfile_canonical security scalar).2, zero_div]

theorem safePairProfile_safe_square (security : ℕ) (scalar : ℤ) :
    (∑ first : SafePalette security, ∑ second : SafePalette security,
      safePairProfile security scalar first.val second.val ^ 2) =
      ∑ first, ∑ second, safePairProfile security scalar first second ^ 2 := by
  have hrow (first : ActualControls.Palette security) :
      (∑ second : SafePalette security, safePairProfile security scalar first second.val ^ 2) =
        ∑ second, safePairProfile security scalar first second ^ 2 := by
    apply safe_sum_eq security (fun second => safePairProfile security scalar first second ^ 2)
    intro color hunsafe
    rw [safePairProfile_zero_outside security scalar first color (Or.inr hunsafe), zero_pow (by decide : 2 ≠ 0)]
  simp only [hrow]
  apply safe_sum_eq security (fun first => ∑ second, safePairProfile security scalar first second ^ 2)
  intro color hunsafe
  simp only [safePairProfile_zero_outside security scalar color _ (Or.inl hunsafe),
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]

theorem bodyPairDensity_square_bound (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (∑ first, ∑ second, (bodyReference security).weight first * (bodyReference security).weight second *
      bodyPairDensity security scalar first second ^ 2) ≤
      4 * (Parameters.modulus security : ℝ) ^ 2 /
        ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) - deletion security)) := by
  have hq := FirstResponse.modulus_pos security
  have hpoint (first second : SafePalette security) :
      (bodyReference security).weight first * (bodyReference security).weight second *
          bodyPairDensity security scalar first second ^ 2 ≤
        4 * (Parameters.modulus security : ℝ) ^ 2 * safePairProfile security scalar first.val second.val ^ 2 := by
    have hden : 1 / (4 * (Parameters.modulus security : ℝ) ^ 2) ≤
        (bodyReference security).weight first * (bodyReference security).weight second := by
      have h := mul_le_mul (bodyReference_lower security first) (bodyReference_lower security second)
        (by positivity : (0 : ℝ) ≤ 1 / (2 * (Parameters.modulus security : ℝ)))
        (bodyReference_positive security first).le
      convert h using 1; ring
    calc
      _ = safePairProfile security scalar first.val second.val ^ 2 /
          ((bodyReference security).weight first * (bodyReference security).weight second) := by
        unfold bodyPairDensity
        field_simp [(bodyReference_positive security first).ne', (bodyReference_positive security second).ne']
      _ ≤ safePairProfile security scalar first.val second.val ^ 2 /
          (1 / (4 * (Parameters.modulus security : ℝ) ^ 2)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
      _ = _ := by field_simp [hq.ne']
  calc
    _ ≤ ∑ first, ∑ second,
        4 * (Parameters.modulus security : ℝ) ^ 2 * safePairProfile security scalar first.val second.val ^ 2 :=
      Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ => hpoint first second
    _ = 4 * (Parameters.modulus security : ℝ) ^ 2 *
        ∑ first, ∑ second, safePairProfile security scalar first second ^ 2 := by
      simp only [← Finset.mul_sum]
      rw [safePairProfile_safe_square]
    _ ≤ 4 * (Parameters.modulus security : ℝ) ^ 2 *
        (1 / ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) - deletion security))) :=
      mul_le_mul_of_nonneg_left (safePairProfile_counting_square security scalar hscalar) (by positivity)
    _ = _ := by ring

theorem bodyPairDensity_square_growth (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (∑ first, ∑ second, (bodyReference security).weight first * (bodyReference security).weight second *
      bodyPairDensity security scalar first second ^ 2) ≤
        1048576 * (Parameters.base security : ℝ) ^ 16 := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have ha : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hd : (Parameters.modulus security : ℝ) / 2 ≤ (Parameters.modulus security : ℝ) - deletion security := by
    have h := Nat.cast_le (α := ℝ).mpr (two_deletion_le_modulus security)
    push_cast at h
    linarith
  have hqu : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  calc
    _ ≤ 4 * (Parameters.modulus security : ℝ) ^ 2 /
        ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) - deletion security)) :=
      bodyPairDensity_square_bound security scalar hscalar
    _ ≤ 4 * (Parameters.modulus security : ℝ) ^ 2 /
        ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) / 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left hd ha.le)
    _ = 8 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by field_simp; ring
    _ ≤ 8 * (131072 * (Parameters.base security : ℝ) ^ 64) / Parameters.anchorWidth security :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqu (by norm_num)) ha.le
    _ = _ := by rw [anchorWidth_eq, Nat.cast_pow]; field_simp; ring

theorem bodyPairDensity_norm_growth (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    Real.sqrt (∑ first, ∑ second, (bodyReference security).weight first * (bodyReference security).weight second *
      bodyPairDensity security scalar first second ^ 2) ≤
        1024 * (Parameters.base security : ℝ) ^ 8 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  convert bodyPairDensity_square_growth security scalar hscalar using 1; ring

def smoothingBudget (security : ℕ) : ℝ :=
  16 * (Parameters.modulus security : ℝ) * Parameters.sourceCutoff security /
    (((Parameters.modulus security : ℝ) / 2) ^ 2 * (Parameters.anchorWidth security : ℝ) ^ 2) +
  16 * (Parameters.modulus security : ℝ) * (Parameters.sourceCutoff security : ℝ) ^ 2 /
    (((Parameters.modulus security : ℝ) / 2) ^ 4 * Parameters.anchorWidth security) +
  8 * (Parameters.sourceCutoff security : ℝ) /
    (((Parameters.modulus security : ℝ) / 2) ^ 2 * Parameters.anchorWidth security)

theorem smoothingBudget_scaled (security : ℕ) :
    (Parameters.modulus security : ℝ) ^ 2 * smoothingBudget security =
      64 * (Parameters.modulus security : ℝ) * Parameters.sourceCutoff security /
        (Parameters.anchorWidth security : ℝ) ^ 2 +
      256 * (Parameters.sourceCutoff security : ℝ) ^ 2 /
        ((Parameters.modulus security : ℝ) * Parameters.anchorWidth security) +
      32 * (Parameters.sourceCutoff security : ℝ) / Parameters.anchorWidth security := by
  have hq := (FirstResponse.modulus_pos security).ne'
  have ha : (Parameters.anchorWidth security : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (InwardAnchor.anchorWidth_pos security).ne'
  unfold smoothingBudget
  field_simp
  ring

theorem smoothingBudget_scaled_decay (security : ℕ) :
    (Parameters.modulus security : ℝ) ^ 2 * smoothingBudget security ≤
      8388896 / (Parameters.base security : ℝ) ^ 30 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hq := FirstResponse.modulus_pos security
  have hqu : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hql : (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
    have h := (Parameters.modulus_bounds security).1
    have hpow : 0 < Parameters.base security ^ 64 := pow_pos (Parameters.base_pos security) _
    exact_mod_cast (show Parameters.base security ^ 64 ≤ Parameters.modulus security by omega)
  rw [smoothingBudget_scaled, Parameters.sourceCutoff, anchorWidth_eq]
  simp only [Nat.cast_pow]
  calc
    _ ≤ 64 * (131072 * (Parameters.base security : ℝ) ^ 64) * (Parameters.base security : ℝ) ^ 2 /
        ((Parameters.base security : ℝ) ^ 48) ^ 2 +
      256 * ((Parameters.base security : ℝ) ^ 2) ^ 2 /
        ((Parameters.base security : ℝ) ^ 64 * (Parameters.base security : ℝ) ^ 48) +
      32 * (Parameters.base security : ℝ) ^ 2 / (Parameters.base security : ℝ) ^ 48 := by
      apply add_le_add _ le_rfl
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqu (by norm_num)) (by positivity)
      · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hql (by positivity))
    _ = 8388608 / (Parameters.base security : ℝ) ^ 30 +
        256 / (Parameters.base security : ℝ) ^ 108 +
        32 / (Parameters.base security : ℝ) ^ 46 := by field_simp; ring
    _ ≤ 8388608 / (Parameters.base security : ℝ) ^ 30 +
        256 / (Parameters.base security : ℝ) ^ 30 +
        32 / (Parameters.base security : ℝ) ^ 30 := by
      apply add_le_add
      · exact add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega)))
      · exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega))
    _ = _ := by ring

theorem liftedPairProfile_scaled_smoothing_decay (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (Parameters.modulus security : ℝ) ^ 2 *
      (∑ color, (smoothProfile (rootPairLaw security) (rootPairShift security) (liftedPairProfile security scalar) color -
        liftedPairProfile security scalar color) ^ 2) ≤
      8388896 / (Parameters.base security : ℝ) ^ 30 :=
  (mul_le_mul_of_nonneg_left (liftedPairProfile_smoothing_square security scalar hscalar)
    (sq_nonneg _)).trans (smoothingBudget_scaled_decay security)

end

end CurrentAFT.DiffusePairBounds

import CurrentAFT.ProposalPositivity

/-!
# Actual clipped activation and primary heights

A literal subwindow of the same discrete Gaussian lower-bounds its
normalizer. This proves the inverse-width upper bound on the actual
activation, complementing the already proved lower bound. The actual
primary height then follows from its balancing numerator.
-/

namespace CurrentAFT.GaussianHeights

open AFT GaussianSource DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

theorem windowNormalizer_lower (width cutoff : ℕ) (hwidth : 0 < width)
    (hcutoff : width - 1 ≤ cutoff) :
    (width : ℝ) * Real.exp (-Real.pi) ≤ windowNormalizer width cutoff := by
  let point : Fin width → Window cutoff := fun index =>
    ⟨(index.val : ℤ), Finset.mem_Icc.mpr ⟨by omega, by have := index.isLt; omega⟩⟩
  have hinjective : Function.Injective point := by
    intro first second hequal
    apply Fin.ext
    have h := congrArg (fun value : Window cutoff => value.val) hequal
    change (first.val : ℤ) = (second.val : ℤ) at h
    exact_mod_cast h
  have hweight (index : Fin width) : Real.exp (-Real.pi) ≤ weight width (point index) := by
    have hw : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
    have hz : (0 : ℝ) ≤ index.val := Nat.cast_nonneg _
    have hzUpper : (index.val : ℝ) ≤ width := Nat.cast_le.mpr index.isLt.le
    have hsquare : (index.val : ℝ) ^ 2 ≤ (width : ℝ) ^ 2 := by nlinarith
    have hproduct := mul_le_mul_of_nonneg_left hsquare
      (div_nonneg Real.pi_pos.le (sq_nonneg (width : ℝ)))
    have hcancel : Real.pi / (width : ℝ) ^ 2 * (width : ℝ) ^ 2 = Real.pi := by
      field_simp
    rw [hcancel] at hproduct
    unfold weight
    apply Real.exp_le_exp.mpr
    change -Real.pi ≤ -(Real.pi / (width : ℝ) ^ 2) * (index.val : ℝ) ^ 2
    linarith
  have hsubset : Finset.univ.image point ⊆ (Finset.univ : Finset (Window cutoff)) := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun value _ _ => (weight_pos (width : ℝ) value).le)
  rw [Finset.sum_image (fun first _ second _ hequal => hinjective hequal)] at hsum
  calc
    _ = ∑ _index : Fin width, Real.exp (-Real.pi) := by simp
    _ ≤ ∑ index : Fin width, weight width (point index) :=
      Finset.sum_le_sum (fun index _ => hweight index)
    _ ≤ _ := hsum

theorem windowGaussian_zero_upper (width cutoff : ℕ) (hwidth : 0 < width)
    (hcutoff : width - 1 ≤ cutoff) :
    (windowGaussian width cutoff).weight (windowZero cutoff) ≤ Real.exp Real.pi / width := by
  have hw : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
  rw [windowGaussian_zero]
  calc
    _ ≤ 1 / ((width : ℝ) * Real.exp (-Real.pi)) :=
      one_div_le_one_div_of_le (mul_pos hw (Real.exp_pos _))
        (windowNormalizer_lower width cutoff hwidth hcutoff)
    _ = _ := by rw [Real.exp_neg]; field_simp

theorem activation_upper (security : ℕ) :
    DiffuseProfiles.activation security ≤ Real.exp Real.pi / (2 * (Parameters.base security : ℝ)) := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hcutoff : Parameters.base security - 1 ≤ Parameters.sourceCutoff security - 1 := by
    unfold Parameters.sourceCutoff
    have hpower : Parameters.base security ≤ Parameters.base security ^ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hb (by omega : 1 ≤ 2)
    omega
  have h := mul_le_mul_of_nonneg_left
    (windowGaussian_zero_upper (Parameters.base security) (Parameters.sourceCutoff security - 1)
      (Parameters.base_pos security) hcutoff) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  change (1 / 2) * (windowGaussian (Parameters.base security)
    (Parameters.sourceCutoff security - 1)).weight (windowZero _) ≤ _
  exact h.trans_eq (by ring)

theorem primaryProfile_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    primaryProfile security color ≤ (Parameters.dimension security : ℝ) /
      (markMass security * Parameters.modulus security) := by
  have hfirst : 0 ≤ (freeMass security + markMass security) * (bodyLaw security false).weight color :=
    mul_nonneg (add_nonneg (freeMass_nonneg security) (markMass_pos security).le)
      ((bodyLaw security false).nonneg color)
  have hsecond : 0 ≤ ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
      (bodyLaw security true).weight color :=
    mul_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ((bodyLaw security true).nonneg color)
  have hthird : 0 ≤ 2 * (Parameters.legCount security : ℝ) * (1 - DiffuseProfiles.activation security) * diffuseMean security color :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by linarith [activation_le_half security])) (diffuseMean_nonneg security color)
  unfold primaryProfile
  calc
    _ ≤ ((Parameters.dimension security : ℝ) / Parameters.modulus security) / markMass security :=
      div_le_div_of_nonneg_right (by linarith) (markMass_pos security).le
    _ = _ := by ring

theorem primaryLaw_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (primaryLaw security).weight color ≤ (Parameters.dimension security : ℝ) /
      (markMass security * Parameters.modulus security) := by
  simpa only [primaryLaw] using primaryProfile_upper security color

theorem dimension_leg_ratio (security : ℕ) :
    (Parameters.dimension security : ℝ) / Parameters.legCount security ≤
      131074 * (Parameters.base security : ℝ) ^ 32 := by
  have hl : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
    exact pow_pos (FirstResponse.base_pos security) _
  apply (div_le_iff₀ hl).mpr
  have hdim : (Parameters.dimension security : ℝ) ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := by
    exact_mod_cast (Parameters.dimension_bounds security).2
  convert hdim using 1
  rw [Parameters.legCount_eq, Nat.cast_pow, mul_assoc, ← pow_add]

/-- The activated marked-primary density has the required coarse local
Hilbert scale. This uses the actual Gaussian upper zero-atom bound. -/
theorem activated_primary_height (security : ℕ) (color : Fin (Parameters.modulus security)) :
    DiffuseProfiles.activation security ^ 2 * (Parameters.modulus security : ℝ) *
      (primaryLaw security).weight color ≤
        65537 * Real.exp Real.pi * (Parameters.base security : ℝ) ^ 31 := by
  have hq := FirstResponse.modulus_pos security
  have hb := FirstResponse.base_pos security
  have ha := DiffuseProfiles.activation_pos security
  have hl : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
    exact pow_pos hb _
  have hfirst := mul_le_mul_of_nonneg_left (primaryLaw_upper security color)
    (show 0 ≤ DiffuseProfiles.activation security ^ 2 * (Parameters.modulus security : ℝ) by positivity)
  have hcancel : DiffuseProfiles.activation security ^ 2 * (Parameters.modulus security : ℝ) *
      ((Parameters.dimension security : ℝ) / (markMass security * Parameters.modulus security)) =
        DiffuseProfiles.activation security * ((Parameters.dimension security : ℝ) / Parameters.legCount security) := by
    unfold markMass
    field_simp
  rw [hcancel] at hfirst
  calc
    _ ≤ DiffuseProfiles.activation security * ((Parameters.dimension security : ℝ) / Parameters.legCount security) := hfirst
    _ ≤ (Real.exp Real.pi / (2 * (Parameters.base security : ℝ))) *
        (131074 * (Parameters.base security : ℝ) ^ 32) :=
      mul_le_mul (activation_upper security) (dimension_leg_ratio security)
        (div_nonneg (Nat.cast_nonneg _) hl.le) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp; ring

end

end CurrentAFT.GaussianHeights

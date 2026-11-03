import CurrentAFT.ProposalPositivity
import CurrentAFT.InwardAnchor

/-!
# Actual proposal deviations and its smoothed-anchor mean

Every body profile below is the actual cyclic pushforward mixture from
`ProposalPrimary`, and both diffuse profiles are the genuine trimmed-slice
mixtures. Their complete L1 estimates are substituted into the actual
balancing numerator. The anchor mean then uses the finite kernel whose
height and row sum were derived from its actual random draws.
-/

namespace CurrentAFT.ProposalPrimary

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.bodySize Parameters.legCount Parameters.dimension Parameters.safeMargin
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile DiffuseProfiles.activation
  DiffuseProfiles.actualSeedLaw primaryProfile primaryLaw safeLaw bodyLaw

theorem safeLaw_l1_uniform (security : ℕ) :
    (∑ color, |(safeLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) =
      4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ) := by
  have hwidth : 2 * (Parameters.safeMargin security : ℤ) + |(0 : ℤ)| < Parameters.modulus security := by
    have h := safe_clearance security
    simp only [abs_zero]
    omega
  have h := TrimmedSlice.law_palette_l1 (Parameters.modulus security)
    (Parameters.safeMargin security) 0 (Int.natCast_nonneg _) hwidth
  simp only [safeLaw, TrimmedSlice.finiteLaw_weight]
  convert h using 1
  push_cast
  ring

theorem shifted_safeLaw_l1_uniform (security : ℕ) (shift : ℤ) :
    (∑ color, |((safeLaw security).map (shiftEquiv security shift)).weight color -
      (Parameters.modulus security : ℝ)⁻¹|) =
        4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ) := by
  simp only [FiniteDist.map_equiv_weight]
  rw [(shiftEquiv security shift).symm.sum_comp
    (fun color => |(safeLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|)]
  exact safeLaw_l1_uniform security

/-- The actual root and scalar convolutions are mixtures of cyclic
equivalences, so the entire L1 error has no root-support factor. -/
theorem bodyLaw_l1_uniform (security : ℕ) (includeScalar : Bool) :
    (∑ color, |(bodyLaw security includeScalar).weight color -
      (Parameters.modulus security : ℝ)⁻¹|) ≤
        4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ) := by
  let shifted (seed : ActualSeed security) := (safeLaw security).map
    (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0))
  have hpoint (color) : (bodyLaw security includeScalar).weight color -
      (Parameters.modulus security : ℝ)⁻¹ =
      ∑ seed, (actualSeedLaw security).weight seed *
        ((shifted seed).weight color - (Parameters.modulus security : ℝ)⁻¹) := by
    simp only [bodyLaw, FiniteDist.mix_weight, shifted, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  calc
    _ ≤ ∑ color, ∑ seed, (actualSeedLaw security).weight seed *
        |(shifted seed).weight color - (Parameters.modulus security : ℝ)⁻¹| := by
      apply Finset.sum_le_sum
      intro color _
      rw [hpoint]
      simpa only [abs_mul, abs_of_nonneg (FiniteDist.nonneg _ _)] using
        Finset.abs_sum_le_sum_abs (fun seed => (actualSeedLaw security).weight seed *
          ((shifted seed).weight color - (Parameters.modulus security : ℝ)⁻¹)) Finset.univ
    _ = ∑ seed, (actualSeedLaw security).weight seed *
        (4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro seed _
      rw [← Finset.mul_sum]
      congr 1
      exact shifted_safeLaw_l1_uniform security _
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem diffuseMean_l1_uniform (security : ℕ) :
    (∑ color, |diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹|) ≤
      2 * (deletion security : ℝ) / Parameters.modulus security := by
  have hpoint (color : Fin (Parameters.modulus security)) :
      |diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹| ≤
      (|actualProfile security true color - (Parameters.modulus security : ℝ)⁻¹| +
        |actualProfile security false color - (Parameters.modulus security : ℝ)⁻¹|) / 2 := by
    rw [show diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹ =
      ((actualProfile security true color - (Parameters.modulus security : ℝ)⁻¹) +
        (actualProfile security false color - (Parameters.modulus security : ℝ)⁻¹)) / 2 by
      unfold diffuseMean; ring]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  calc
    _ ≤ ∑ color,
        (|actualProfile security true color - (Parameters.modulus security : ℝ)⁻¹| +
          |actualProfile security false color - (Parameters.modulus security : ℝ)⁻¹|) / 2 :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ ≤ _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      linarith [actualProfile_l1_uniform security true, actualProfile_l1_uniform security false]

/-- The explicit L1 budget printed in the current proposal proof. -/
def primaryDeviationBudget (security : ℕ) : ℝ :=
  4 * ((Parameters.bodySize security : ℝ) + markMass security) * Parameters.safeMargin security /
    (markMass security * Parameters.modulus security) +
  4 * (1 - activation security) * deletion security /
    (activation security * Parameters.modulus security)

theorem primaryLaw_l1_uniform (security : ℕ) :
    (∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) ≤
      primaryDeviationBudget security := by
  have hq := FirstResponse.modulus_pos security
  have hm := markMass_pos security
  have ha := activation_pos security
  have hl : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact_mod_cast pow_pos (Parameters.base_pos security) 128
  have hfirst : 0 ≤ freeMass security + markMass security :=
    add_nonneg (freeMass_nonneg security) hm.le
  have hsecond : 0 ≤ (Parameters.legCount security : ℝ) + Parameters.modulus security := by positivity
  have hthird : 0 ≤ 2 * (Parameters.legCount security : ℝ) * (1 - activation security) :=
    mul_nonneg (by positivity) (by linarith [activation_le_half security])
  have hidentity (color : Fin (Parameters.modulus security)) :
      (primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹ =
      -((freeMass security + markMass security) *
          ((bodyLaw security false).weight color - (Parameters.modulus security : ℝ)⁻¹) +
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
          ((bodyLaw security true).weight color - (Parameters.modulus security : ℝ)⁻¹) +
        2 * Parameters.legCount security * (1 - activation security) *
          (diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹)) / markMass security := by
    simp only [primaryLaw]
    unfold primaryProfile freeMass markMass
    simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  have hpoint (color : Fin (Parameters.modulus security)) :
      |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹| ≤
      ((freeMass security + markMass security) *
          |(bodyLaw security false).weight color - (Parameters.modulus security : ℝ)⁻¹| +
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
          |(bodyLaw security true).weight color - (Parameters.modulus security : ℝ)⁻¹| +
        2 * Parameters.legCount security * (1 - activation security) *
          |diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹|) / markMass security := by
    rw [hidentity, abs_div, abs_neg, abs_of_pos hm]
    apply div_le_div_of_nonneg_right _ hm.le
    have htriangle := (abs_add_le
      ((freeMass security + markMass security) *
        ((bodyLaw security false).weight color - (Parameters.modulus security : ℝ)⁻¹) +
       ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
        ((bodyLaw security true).weight color - (Parameters.modulus security : ℝ)⁻¹))
      (2 * Parameters.legCount security * (1 - activation security) *
        (diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    simpa only [abs_mul, abs_of_nonneg hfirst, abs_of_nonneg hsecond,
      abs_of_nonneg hthird] using htriangle
  calc
    _ ≤ ∑ color,
        ((freeMass security + markMass security) *
            |(bodyLaw security false).weight color - (Parameters.modulus security : ℝ)⁻¹| +
          ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
            |(bodyLaw security true).weight color - (Parameters.modulus security : ℝ)⁻¹| +
          2 * Parameters.legCount security * (1 - activation security) *
            |diffuseMean security color - (Parameters.modulus security : ℝ)⁻¹|) / markMass security :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ ≤ ((freeMass security + markMass security) *
          (4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ)) +
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
          (4 * Parameters.safeMargin security / (Parameters.modulus security : ℝ)) +
        2 * Parameters.legCount security * (1 - activation security) *
          (2 * (deletion security : ℝ) / Parameters.modulus security)) / markMass security := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      apply div_le_div_of_nonneg_right _ hm.le
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (bodyLaw_l1_uniform security false) hfirst)
        (mul_le_mul_of_nonneg_left (bodyLaw_l1_uniform security true) hsecond))
        (mul_le_mul_of_nonneg_left (diffuseMean_l1_uniform security) hthird)
    _ = primaryDeviationBudget security := by
      unfold primaryDeviationBudget freeMass markMass
      field_simp
      ring

/-- The actual smoothed-anchor image of the current primary law. -/
def anchorPrimaryMean (security : ℕ) (output : Fin (Parameters.modulus security)) : ℝ :=
  ∑ color, (InwardAnchor.smoothedAnchorLaw security color).weight output * (primaryLaw security).weight color

theorem anchorPrimaryMean_nonneg (security : ℕ) (output : Fin (Parameters.modulus security)) :
    0 ≤ anchorPrimaryMean security output :=
  Finset.sum_nonneg (fun color _ => mul_nonneg
    ((InwardAnchor.smoothedAnchorLaw security color).nonneg output) ((primaryLaw security).nonneg color))

theorem anchorPrimaryMean_mass (security : ℕ) : ∑ output, anchorPrimaryMean security output = 1 := by
  unfold anchorPrimaryMean
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  exact FiniteDist.sum_one _

/-- Row sum and height of the actual kernel give the primary-mean
height, using the full L1 deviation of that same primary law. -/
theorem anchorPrimaryMean_height (security : ℕ) (output : Fin (Parameters.modulus security)) :
    anchorPrimaryMean security output ≤ 2 / (Parameters.modulus security : ℝ) +
      (∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) /
        Parameters.anchorWidth security := by
  have hq := FirstResponse.modulus_pos security
  have hpoint (color : Fin (Parameters.modulus security)) :
      (InwardAnchor.smoothedAnchorLaw security color).weight output * (primaryLaw security).weight color ≤
      (InwardAnchor.smoothedAnchorLaw security color).weight output * (Parameters.modulus security : ℝ)⁻¹ +
      (1 / (Parameters.anchorWidth security : ℝ)) *
        |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹| := by
    have hdeviation := mul_le_mul_of_nonneg_left
      (le_abs_self ((primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹))
      ((InwardAnchor.smoothedAnchorLaw security color).nonneg output)
    have hheight := mul_le_mul_of_nonneg_right
      (InwardAnchor.smoothedAnchorLaw_height security color output)
      (abs_nonneg ((primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹))
    nlinarith only [hdeviation, hheight]
  calc
    _ ≤ ∑ color,
        ((InwardAnchor.smoothedAnchorLaw security color).weight output * (Parameters.modulus security : ℝ)⁻¹ +
        (1 / (Parameters.anchorWidth security : ℝ)) *
          |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      have hrow := mul_le_mul_of_nonneg_right
        (InwardAnchor.smoothedAnchorLaw_row_sum_le_two security output) (inv_nonneg.mpr hq.le)
      have hsame : (1 / (Parameters.anchorWidth security : ℝ)) *
          (∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) =
        (∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) /
          Parameters.anchorWidth security := by ring
      rw [hsame]
      simpa only [div_eq_mul_inv] using add_le_add hrow
        (le_refl ((∑ color, |(primaryLaw security).weight color - (Parameters.modulus security : ℝ)⁻¹|) /
          Parameters.anchorWidth security))

theorem anchorPrimaryMean_height_budget (security : ℕ) (output : Fin (Parameters.modulus security)) :
    anchorPrimaryMean security output ≤ 2 / (Parameters.modulus security : ℝ) +
      primaryDeviationBudget security / Parameters.anchorWidth security :=
  (anchorPrimaryMean_height security output).trans
    (add_le_add le_rfl (div_le_div_of_nonneg_right (primaryLaw_l1_uniform security)
      (Nat.cast_nonneg _)))

/-- The current numerical sizes absorb the large body population into
the genuine anchor width. This is an arithmetic theorem for that family. -/
theorem body_margin_anchor_budget (security : ℕ) :
    Parameters.bodySize security * Parameters.safeMargin security ≤
      24 * Parameters.legCount security * Parameters.anchorWidth security := by
  have hlarge : 16384 ≤ Parameters.base security ^ 14 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 14
    norm_num at h
    exact h
  have hq := (Parameters.modulus_bounds security).2
  rw [Parameters.bodySize_eq, Parameters.safeMargin, Parameters.sourceCutoff,
    Parameters.legCount_eq, anchorWidth_eq]
  calc
    _ = 3 * Parameters.modulus security * Parameters.base security ^ 98 := by ring
    _ ≤ 3 * (131072 * Parameters.base security ^ 64) * Parameters.base security ^ 98 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq)
    _ = 393216 * Parameters.base security ^ 162 := by ring
    _ ≤ (24 * Parameters.base security ^ 14) * Parameters.base security ^ 162 :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

theorem safeMargin_le_anchorWidth (security : ℕ) :
    Parameters.safeMargin security ≤ Parameters.anchorWidth security := by
  have h := InwardAnchor.four_cutoffs_le_anchor security
  rw [Parameters.safeMargin]
  omega

theorem markMass_le_legCount (security : ℕ) :
    markMass security ≤ Parameters.legCount security := by
  have hactivation : activation security ≤ 1 := (activation_le_half security).trans (by norm_num)
  simpa only [markMass, mul_one] using mul_le_mul_of_nonneg_left hactivation
    (Nat.cast_nonneg (Parameters.legCount security) : (0 : ℝ) ≤ Parameters.legCount security)

theorem body_mark_margin_anchor_budget (security : ℕ) :
    ((Parameters.bodySize security : ℝ) + markMass security) * Parameters.safeMargin security ≤
      25 * Parameters.legCount security * Parameters.anchorWidth security := by
  have hbody : (Parameters.bodySize security : ℝ) * Parameters.safeMargin security ≤
      24 * Parameters.legCount security * Parameters.anchorWidth security := by
    exact_mod_cast body_margin_anchor_budget security
  have hmargin : (Parameters.safeMargin security : ℝ) ≤ Parameters.anchorWidth security := by
    exact_mod_cast safeMargin_le_anchorWidth security
  have hmark := mul_le_mul_of_nonneg_right (markMass_le_legCount security)
    (Nat.cast_nonneg (Parameters.safeMargin security) : (0 : ℝ) ≤ Parameters.safeMargin security)
  have hleg := mul_le_mul_of_nonneg_left hmargin
    (Nat.cast_nonneg (Parameters.legCount security) : (0 : ℝ) ≤ Parameters.legCount security)
  nlinarith only [hbody, hmark, hleg]

/-- The actual primary mean obeys a dimension-free activated height
bound. Every input is the concrete law already constructed above. -/
theorem activated_anchorPrimaryMean_height (security : ℕ)
    (output : Fin (Parameters.modulus security)) :
    activation security * anchorPrimaryMean security output ≤
      128 / (Parameters.modulus security : ℝ) := by
  have hq := FirstResponse.modulus_pos security
  have ha := activation_pos security
  have hwidth : (0 : ℝ) < Parameters.anchorWidth security :=
    Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hlegs : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact_mod_cast pow_pos (Parameters.base_pos security) 128
  have hmargin := body_mark_margin_anchor_budget security
  have hdelete : (deletion security : ℝ) ≤ 6 * Parameters.anchorWidth security := by
    have h := FirstResponse.deletion_le_six_anchor security
    rw [← anchorWidth_eq] at h
    exact_mod_cast h
  have hfirst : 4 * ((Parameters.bodySize security : ℝ) + markMass security) *
      Parameters.safeMargin security /
        ((Parameters.legCount security : ℝ) * Parameters.anchorWidth security) ≤ 100 := by
    apply (div_le_iff₀ (mul_pos hlegs hwidth)).mpr
    nlinarith only [hmargin]
  have hsecond : 4 * (1 - activation security) * deletion security /
      (Parameters.anchorWidth security : ℝ) ≤ 24 := by
    apply (div_le_iff₀ hwidth).mpr
    have hproduct := mul_nonneg ha.le (Nat.cast_nonneg (deletion security) : (0 : ℝ) ≤ deletion security)
    nlinarith only [hdelete, hproduct]
  have hidentity : activation security *
      (2 / (Parameters.modulus security : ℝ) + primaryDeviationBudget security /
        Parameters.anchorWidth security) * Parameters.modulus security =
      2 * activation security +
        4 * ((Parameters.bodySize security : ℝ) + markMass security) * Parameters.safeMargin security /
          ((Parameters.legCount security : ℝ) * Parameters.anchorWidth security) +
        4 * (1 - activation security) * deletion security / Parameters.anchorWidth security := by
    unfold primaryDeviationBudget markMass
    field_simp
    ring
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (anchorPrimaryMean_height_budget security output) ha.le) hq.le
  apply (le_div_iff₀ hq).mpr
  rw [hidentity] at hscaled
  have halower := activation_le_half security
  linarith

end

end CurrentAFT.ProposalPrimary

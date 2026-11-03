import CurrentAFT.ProposalCenter
import CurrentAFT.ProposalDeviation

/-!
# The actual fringe and its primary certificate

The fringe is the gap between the true root-convolved safe profile and
the safe-interval height. A strengthened estimate on the actual primary
numerator dominates that gap by the actual compensation times primary
law. This proves the weighted Hilbert bounds, rather than postulating a
small background coefficient. The certificate is then constructed with
the explicit current first-response inverse.
-/

namespace CurrentAFT.FringeCertificate

open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.bodySize Parameters.legCount Parameters.dimension Parameters.safeMargin
  DiffuseProfiles.activation centerLaw primaryProfile safeLaw bodyLaw
  FirstResponse.responseEquiv

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

def uniformProfile (security : ℕ) : Palette security → ℝ :=
  fun _ => (Parameters.modulus security : ℝ)⁻¹

def fringe (security : ℕ) (color : Palette security) : ℝ :=
  safeHeight security - (bodyLaw security false).weight color

def fringeMass (security : ℕ) : ℝ :=
  2 * Parameters.safeMargin security /
    ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)

theorem fringe_nonneg (security : ℕ) (color : Palette security) : 0 ≤ fringe security color :=
  sub_nonneg.mpr (bodyLaw_upper security false color)

theorem fringe_sum_height (security : ℕ) :
    (∑ color, fringe security color) = (Parameters.modulus security : ℝ) * safeHeight security - 1 := by
  simp only [fringe, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, FiniteDist.sum_one]

theorem fringeMass_height (security : ℕ) :
    fringeMass security = (Parameters.modulus security : ℝ) * safeHeight security - 1 := by
  have hden : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  unfold fringeMass safeHeight
  field_simp
  ring

theorem fringe_sum (security : ℕ) : ∑ color, fringe security color = fringeMass security := by
  rw [fringe_sum_height, fringeMass_height]

theorem fringeMass_nonneg (security : ℕ) : 0 ≤ fringeMass security := by
  rw [← fringe_sum]
  exact Finset.sum_nonneg (fun color _ => fringe_nonneg security color)

/-- Keeping the true `B0` term in the primary balancing numerator
gives the fringe contribution before any coarse pointwise replacement. -/
theorem primaryProfile_fringe_lower (security : ℕ) (color : Palette security) :
    ((freeMass security + markMass security) / markMass security) * fringe security color +
      (1 - baselineLoss security) / Parameters.modulus security ≤ (primaryLaw security).weight color := by
  have hm := markMass_pos security
  have hq := FirstResponse.modulus_pos security
  have ha := activation_pos security
  have hlegs : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact_mod_cast pow_pos (Parameters.base_pos security) 128
  have hsafe : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hdiff : (0 : ℝ) < Parameters.modulus security - deletion security :=
    sub_pos.mpr (Nat.cast_lt.mpr (deletion_clearance security))
  have hc1 : 0 ≤ (Parameters.legCount security : ℝ) + Parameters.modulus security := by positivity
  have hc2 : 0 ≤ 2 * (Parameters.legCount security : ℝ) * (1 - activation security) :=
    mul_nonneg (by positivity) (by linarith [activation_le_half security])
  have h1 := mul_le_mul_of_nonneg_left (bodyLaw_upper security true color) hc1
  have h2 := mul_le_mul_of_nonneg_left (diffuseMean_upper security color) hc2
  rw [mul_one_div] at h2
  have hidentity :
      (((freeMass security + markMass security) / markMass security) * fringe security color +
        (1 - baselineLoss security) / Parameters.modulus security) * markMass security =
      (Parameters.dimension security : ℝ) / Parameters.modulus security -
        (freeMass security + markMass security) * (bodyLaw security false).weight color -
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) * safeHeight security -
        2 * Parameters.legCount security * (1 - activation security) /
          ((Parameters.modulus security : ℝ) - deletion security) := by
    unfold fringe baselineLoss safeHeight freeMass markMass
    simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  simp only [primaryLaw]
  unfold primaryProfile
  apply (le_div_iff₀ hm).mpr
  rw [hidentity]
  linarith

/-- The actual fringe is pointwise dominated by compensation times
the actual normalized primary law. -/
theorem fringe_majorant (security : ℕ) (color : Palette security) :
    fringe security color ≤ compensation security * (primaryLaw security).weight color := by
  have hc := compensation_nonneg security
  have hf := freeMass_pos security
  have hm := markMass_pos security
  have hq := FirstResponse.modulus_pos security
  have hresidual : 0 ≤ (1 - baselineLoss security) / Parameters.modulus security :=
    div_nonneg (by linarith [baselineLoss_le_half security]) hq.le
  have h := mul_le_mul_of_nonneg_left (primaryProfile_fringe_lower security color) hc
  have hcoefficient : compensation security *
      ((freeMass security + markMass security) / markMass security) = 1 + compensation security := by
    unfold compensation
    field_simp
  rw [mul_add, ← mul_assoc, hcoefficient] at h
  have hfringe := mul_nonneg hc (fringe_nonneg security color)
  have hconstant := mul_nonneg hc hresidual
  nlinarith only [h, hfringe, hconstant]

theorem fringe_profileSquareNorm_le (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (fringe security) ≤
      compensation security * fringeMass security := by
  have hq := FirstResponse.modulus_pos security
  have hp (color : Palette security) : 0 < (primaryLaw security).weight color :=
    (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (primaryProfile_atom_lower security color)
  have h := signProfile_square_bound (primaryLaw security).weight (fringe security)
    (compensation security) hp (fun color => by
      rw [abs_of_nonneg (fringe_nonneg security color)]
      exact fringe_majorant security color)
  simpa only [abs_of_nonneg (fringe_nonneg security _), fringe_sum] using h

def bodyDeviation (security : ℕ) : Palette security → ℝ :=
  fun color => (bodyLaw security false).weight color - uniformProfile security color

theorem bodyDeviation_mass (security : ℕ) : ∑ color, bodyDeviation security color = 0 := by
  have hq := (FirstResponse.modulus_pos security).ne'
  simp only [bodyDeviation, uniformProfile, Finset.sum_sub_distrib, FiniteDist.sum_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  norm_num

theorem bodyDeviation_formula (security : ℕ) :
    bodyDeviation security = fringeMass security • uniformProfile security - fringe security := by
  funext color
  have hq := (FirstResponse.modulus_pos security).ne'
  rw [fringeMass_height]
  simp only [bodyDeviation, fringe, uniformProfile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem uniformProfile_square_le_two (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (uniformProfile security) ≤ 2 := by
  have hq := FirstResponse.modulus_pos security
  have hpoint (color : Palette security) :
      uniformProfile security color ^ 2 / (primaryLaw security).weight color ≤
        2 / (Parameters.modulus security : ℝ) := by
    have hinv := one_div_le_one_div_of_le
      (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ)))
      (primaryProfile_atom_lower security color)
    have hcancel : 1 / (1 / (2 * (Parameters.modulus security : ℝ))) =
        2 * Parameters.modulus security := by simp only [one_div_one_div]
    rw [hcancel] at hinv
    calc
      _ ≤ uniformProfile security color ^ 2 * (2 * Parameters.modulus security) := by
        simpa only [one_div, div_eq_mul_inv, one_mul, primaryLaw] using mul_le_mul_of_nonneg_left hinv
          (sq_nonneg (uniformProfile security color))
      _ = _ := by unfold uniformProfile; field_simp
  unfold profileSquareNorm
  calc
    _ ≤ ∑ _color : Palette security, 2 / (Parameters.modulus security : ℝ) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ = 2 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

theorem profileSquareNorm_sub_le_two (security : ℕ) (first second : Palette security → ℝ) :
    profileSquareNorm (primaryLaw security).weight (first - second) ≤
      2 * profileSquareNorm (primaryLaw security).weight first +
        2 * profileSquareNorm (primaryLaw security).weight second := by
  have hq := FirstResponse.modulus_pos security
  have hp (color : Palette security) : 0 ≤ (primaryLaw security).weight color := (primaryLaw security).nonneg color
  have hpoint (color : Palette security) :
      (first color - second color) ^ 2 / (primaryLaw security).weight color ≤
        2 * (first color ^ 2 / (primaryLaw security).weight color) +
          2 * (second color ^ 2 / (primaryLaw security).weight color) := by
    have hscalar : (first color - second color) ^ 2 ≤ 2 * first color ^ 2 + 2 * second color ^ 2 := by
      nlinarith [sq_nonneg (first color + second color)]
    exact (div_le_div_of_nonneg_right hscalar (hp color)).trans_eq (by ring)
  simpa only [profileSquareNorm, Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum] using
    Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)

/-- The actual root-convolved safe profile has its stronger weighted
Hilbert budget, rather than merely an unweighted boundary-mass estimate. -/
theorem bodyDeviation_profileSquareNorm_le (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (bodyDeviation security) ≤
      4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security := by
  rw [bodyDeviation_formula]
  have h := profileSquareNorm_sub_le_two security
    (fringeMass security • uniformProfile security) (fringe security)
  rw [profileSquareNorm_smul] at h
  have hu := mul_le_mul_of_nonneg_left (uniformProfile_square_le_two security)
    (sq_nonneg (fringeMass security))
  have hf := fringe_profileSquareNorm_le security
  nlinarith only [h, hu, hf]

/-- The primary profile certificate is obtained by an actual finite
linear inverse, then divided by the actual activation. -/
def primaryCertificateProfile (security : ℕ) : Palette security → ℝ :=
  (activation security)⁻¹ • (FirstResponse.responseEquiv security).symm (bodyDeviation security)

def primaryCertificateDensity (security : ℕ) (color : Palette security) : ℝ :=
  primaryCertificateProfile security color / (primaryLaw security).weight color

theorem primaryCertificateProfile_mass (security : ℕ) :
    ∑ color, primaryCertificateProfile security color = 0 := by
  simp only [primaryCertificateProfile, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    FirstResponse.response_inverse_preserves_mass, bodyDeviation_mass, mul_zero]

theorem primaryCertificateDensity_centered (security : ℕ) :
    (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color) = 0 := by
  have hq := FirstResponse.modulus_pos security
  have hp (color : Palette security) : (primaryLaw security).weight color ≠ 0 :=
    ne_of_gt ((by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (primaryProfile_atom_lower security color))
  simp only [primaryCertificateDensity, mul_div_cancel₀ _ (hp _)]
  exact primaryCertificateProfile_mass security

/-- Leading evaluation of this concrete canonical density is exactly
the actual root-convolved safe-profile deviation. -/
theorem primaryCertificateDensity_leading (security : ℕ) :
    activation security • FirstResponse.response security
      (fun color => (primaryLaw security).weight color * primaryCertificateDensity security color) =
        bodyDeviation security := by
  have hq := FirstResponse.modulus_pos security
  have hp (color : Palette security) : (primaryLaw security).weight color ≠ 0 :=
    ne_of_gt ((by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (primaryProfile_atom_lower security color))
  have hdensity : (fun color => (primaryLaw security).weight color * primaryCertificateDensity security color) =
      primaryCertificateProfile security := by
    funext color
    simp only [primaryCertificateDensity, mul_div_cancel₀ _ (hp color)]
  rw [hdensity, primaryCertificateProfile, map_smul]
  have hinverse : FirstResponse.response security
      ((FirstResponse.responseEquiv security).symm (bodyDeviation security)) = bodyDeviation security :=
    by rw [← FirstResponse.responseEquiv_forward]; exact (FirstResponse.responseEquiv security).apply_symm_apply _
  rw [hinverse, smul_smul, mul_inv_cancel₀ (activation_pos security).ne', one_smul]

theorem primaryCertificateDensity_square_bound (security : ℕ) :
    (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) ≤
      (4 / activation security ^ 2) *
        (4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security) := by
  have hq := FirstResponse.modulus_pos security
  have hpositive (profile : Palette security → ℝ) : 0 ≤ profileSquareNorm (primaryLaw security).weight profile :=
    profileSquareNorm_nonneg _ _ (primaryLaw security).nonneg
  have hinverse := (actual_first_response_stable security (bodyDeviation security)).2
  have hinverseSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hinverse 2
  rw [mul_pow, Real.sq_sqrt (hpositive _), Real.sq_sqrt (hpositive _)] at hinverseSq
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hinverseSq
  have hscaled := mul_le_mul_of_nonneg_left
    (hinverseSq.trans (mul_le_mul_of_nonneg_left (bodyDeviation_profileSquareNorm_le security) (by norm_num)))
    (sq_nonneg ((activation security)⁻¹))
  have hdensity : (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) =
      profileSquareNorm (primaryLaw security).weight (primaryCertificateProfile security) := by
    exact densityScore_square _ _
  rw [hdensity, primaryCertificateProfile, profileSquareNorm_smul]
  exact hscaled.trans_eq (by ring)

end

end CurrentAFT.FringeCertificate

import CurrentAFT.FringeCertificate
import CurrentAFT.PairedResponse
import CurrentAFT.BodyResponse

/-!
# Concrete stable atoms for the current free-body background

The primary fringe certificate and the safe-centered body certificate
are built from the actual current laws. Explicit current parameter bounds
give quantitative decay of their genuine density L2 norms. Their leading
responses sum exactly to the actual root-convolved center-law deviation.
No background smallness or response stability is assumed in this file.
-/

namespace CurrentAFT.BackgroundCertificates

open AFT DiffuseProfiles ProposalPrimary FringeCertificate
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.bodySize Parameters.legCount Parameters.safeMargin DiffuseProfiles.activation
  DiffuseProfiles.actualSeedLaw primaryProfile safeLaw bodyLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

theorem fringeMass_decay (security : ℕ) :
    fringeMass security ≤ 1 / (Parameters.base security : ℝ) ^ 62 := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hstrip : 4 * (Parameters.safeMargin security : ℝ) < Parameters.modulus security := by
    exact_mod_cast safe_clearance security
  have hqLower : 65536 * (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_bounds security).1
  have hmargin : (Parameters.safeMargin security : ℝ) = 3 * (Parameters.base security : ℝ) ^ 2 := by
    simp only [Parameters.safeMargin, Parameters.sourceCutoff, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    _ ≤ (2 * Parameters.safeMargin security : ℝ) / ((Parameters.modulus security : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = (12 * (Parameters.base security : ℝ) ^ 2) / Parameters.modulus security := by rw [hmargin]; ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hq (pow_pos hb _)).mpr
      have hsmall : 12 * (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
        nlinarith only [hqLower, pow_nonneg hb.le 64]
      nlinarith only [hsmall]

theorem compensation_decay (security : ℕ) :
    compensation security ≤ 1 / (Parameters.base security : ℝ) ^ 32 := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hqLower : 65536 * (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_bounds security).1
  calc
    _ ≤ (Parameters.legCount security : ℝ) / Parameters.bodySize security := compensation_le_leg_body security
    _ = (Parameters.base security : ℝ) ^ 32 / Parameters.modulus security := by
      simp only [Parameters.legCount_eq, Parameters.bodySize_eq, Nat.cast_pow, Nat.cast_mul]
      field_simp
    _ ≤ _ := by
      apply (div_le_div_iff₀ hq (pow_pos hb _)).mpr
      have hsmall : (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
        nlinarith only [hqLower, pow_nonneg hb.le 64]
      nlinarith only [hsmall]

theorem bodyDeviation_budget_decay (security : ℕ) :
    4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security ≤
      6 / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  have hm := fringeMass_decay security
  have hc := compensation_decay security
  have hmsq := pow_le_pow_left₀ (fringeMass_nonneg security) hm 2
  have hproduct := mul_le_mul hc hm (fringeMass_nonneg security) (by positivity)
  have hpower : 1 / (Parameters.base security : ℝ) ^ 124 ≤ 1 / (Parameters.base security : ℝ) ^ 94 :=
    one_div_le_one_div_of_le (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega))
  have hmsqBound : fringeMass security ^ 2 ≤ 1 / (Parameters.base security : ℝ) ^ 124 :=
    hmsq.trans_eq (by rw [div_pow, one_pow, ← pow_mul])
  have hproductBound : compensation security * fringeMass security ≤
      1 / (Parameters.base security : ℝ) ^ 94 :=
    hproduct.trans_eq (by ring)
  calc
    _ = 4 * fringeMass security ^ 2 + 2 * (compensation security * fringeMass security) := by ring
    _ ≤ 4 * (1 / (Parameters.base security : ℝ) ^ 94) +
        2 * (1 / (Parameters.base security : ℝ) ^ 94) :=
      add_le_add (mul_le_mul_of_nonneg_left (hmsqBound.trans hpower) (by norm_num))
        (mul_le_mul_of_nonneg_left hproductBound (by norm_num))
    _ = _ := by ring

theorem primaryCertificateDensity_square_decay (security : ℕ) :
    (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) ≤
      384 / (Parameters.base security : ℝ) ^ 92 := by
  have hb := FirstResponse.base_pos security
  have hbudget0 : 0 ≤ 4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security :=
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (compensation_nonneg security)) (fringeMass_nonneg security))
  have hinv := FirstResponse.activation_inverse_le security
  have hinvsq := pow_le_pow_left₀ (one_div_pos.mpr (activation_pos security)).le hinv 2
  have hcoefficient : 4 / activation security ^ 2 ≤ 64 * (Parameters.base security : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hinvsq (show (0 : ℝ) ≤ 4 by norm_num)
    convert h using 1 <;> ring
  calc
    _ ≤ (4 / activation security ^ 2) *
        (4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security) :=
      primaryCertificateDensity_square_bound security
    _ ≤ (64 * (Parameters.base security : ℝ) ^ 2) * (6 / (Parameters.base security : ℝ) ^ 94) :=
      mul_le_mul hcoefficient (bodyDeviation_budget_decay security) hbudget0 (by positivity)
    _ = _ := by field_simp; ring

/-- Explicit decay is stronger than the coarse `O(base^-31)` budget. -/
theorem primaryCertificateDensity_norm_decay (security : ℕ) :
    Real.sqrt (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) ≤
      20 / (Parameters.base security : ℝ) ^ 46 := by
  have hb := FirstResponse.base_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hden : (20 / (Parameters.base security : ℝ) ^ 46) ^ 2 =
      400 / (Parameters.base security : ℝ) ^ 92 := by ring
  rw [hden]
  exact (primaryCertificateDensity_square_decay security).trans
    (div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hb.le _))

theorem primaryCertificateDensity_norm_coarse (security : ℕ) :
    Real.sqrt (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) ≤
      20 / (Parameters.base security : ℝ) ^ 31 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  exact (primaryCertificateDensity_norm_decay security).trans
    (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega)))

def bodyCertificateProfile (security : ℕ) : Palette security → ℝ :=
  fun center => (centerLaw security).weight center - (safeLaw security).weight center

def bodyCertificateDensity (security : ℕ) (center : Palette security) : ℝ :=
  bodyCertificateProfile security center / (centerLaw security).weight center

theorem bodyCertificateProfile_mass (security : ℕ) : ∑ center, bodyCertificateProfile security center = 0 := by
  simp only [bodyCertificateProfile, Finset.sum_sub_distrib, FiniteDist.sum_one, sub_self]

theorem bodyCertificateProfile_zero_outside (security : ℕ) (center : Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security center) : bodyCertificateProfile security center = 0 := by
  simp only [bodyCertificateProfile, centerLaw, centerProfile_zero_outside security center hunsafe,
    safeLaw_weight, if_neg hunsafe, sub_self]

theorem bodyCertificateProfile_zero_of_center_zero (security : ℕ) (center : Palette security)
    (hzero : (centerLaw security).weight center = 0) : bodyCertificateProfile security center = 0 := by
  have hbound := (centerProfile_bounds security center).1
  change (safeLaw security).weight center / 2 ≤ (centerLaw security).weight center at hbound
  rw [hzero] at hbound
  have hsafe : (safeLaw security).weight center = 0 := by
    linarith [(safeLaw security).nonneg center]
  simp only [bodyCertificateProfile, hzero, hsafe, sub_self]

theorem bodyCertificateDensity_profile (security : ℕ) :
    (fun center => (centerLaw security).weight center * bodyCertificateDensity security center) =
      bodyCertificateProfile security := by
  funext center
  by_cases hz : (centerLaw security).weight center = 0
  · simp only [hz, zero_mul, bodyCertificateProfile_zero_of_center_zero security center hz]
  · unfold bodyCertificateDensity
    field_simp

theorem bodyCertificateDensity_centered (security : ℕ) :
    (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center) = 0 := by
  rw [bodyCertificateDensity_profile]
  exact bodyCertificateProfile_mass security

theorem bodyCertificateDensity_zero_outside (security : ℕ) (center : Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security center) : bodyCertificateDensity security center = 0 := by
  simp only [bodyCertificateDensity, bodyCertificateProfile_zero_outside security center hunsafe, zero_div]

theorem dominated_profile_square_le (security : ℕ) (reference profile : Palette security → ℝ)
    (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient) (href : ∀ color, 0 ≤ reference color)
    (hprofile : ∀ color, 0 ≤ profile color)
    (hdomination : ∀ color, profile color ≤ coefficient * reference color) :
    profileSquareNorm reference profile ≤ coefficient * ∑ color, profile color := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  by_cases hz : reference color = 0
  · rw [hz, div_zero]
    exact mul_nonneg hcoefficient (hprofile color)
  · have hp : 0 < reference color := lt_of_le_of_ne (href color) (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    have h := mul_le_mul_of_nonneg_right (hdomination color) (hprofile color)
    nlinarith only [h]

theorem safeLaw_center_square_le_two (security : ℕ) :
    profileSquareNorm (centerLaw security).weight (safeLaw security).weight ≤ 2 := by
  have hdom (color : Palette security) : (safeLaw security).weight color ≤
      2 * (centerLaw security).weight color := by
    have h := (centerProfile_bounds security color).1
    change (safeLaw security).weight color / 2 ≤ (centerLaw security).weight color at h
    linarith
  simpa only [FiniteDist.sum_one, mul_one] using dominated_profile_square_le security
    (centerLaw security).weight (safeLaw security).weight 2 (by norm_num)
    (centerLaw security).nonneg (safeLaw security).nonneg hdom

theorem anchorPrimaryMean_center_square_le (security : ℕ) :
    profileSquareNorm (centerLaw security).weight (anchorPrimaryMean security) ≤ 256 / activation security := by
  have ha := activation_pos security
  have hdom (color : Palette security) : anchorPrimaryMean security color ≤
      (256 / activation security) * (centerLaw security).weight color := by
    have h := PairedResponse.activated_anchor_center_comparison security color
    have heq : (256 / activation security) * (centerLaw security).weight color =
        (256 * (centerLaw security).weight color) / activation security := by ring
    rw [heq]
    apply (le_div_iff₀ ha).mpr
    nlinarith only [h]
  simpa only [anchorPrimaryMean_mass, mul_one] using dominated_profile_square_le security
    (centerLaw security).weight (anchorPrimaryMean security) (256 / activation security)
    (by positivity) (centerLaw security).nonneg (anchorPrimaryMean_nonneg security) hdom

theorem bodyCertificateProfile_formula (security : ℕ) :
    bodyCertificateProfile security = compensation security •
      ((safeLaw security).weight - anchorPrimaryMean security) := by
  have hanchor (color : Palette security) : (anchorPrimaryLaw security).weight color =
      anchorPrimaryMean security color := by
    simp only [anchorPrimaryLaw, FiniteDist.mix_weight, anchorPrimaryMean]
    apply Finset.sum_congr rfl
    intro primary _
    ring
  funext color
  simp only [bodyCertificateProfile, centerLaw, centerProfile, hanchor, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem center_profile_sub_square_le_two (security : ℕ) (first second : Palette security → ℝ) :
    profileSquareNorm (centerLaw security).weight (first - second) ≤
      2 * profileSquareNorm (centerLaw security).weight first +
        2 * profileSquareNorm (centerLaw security).weight second := by
  have hpoint (color : Palette security) : (first color - second color) ^ 2 / (centerLaw security).weight color ≤
      2 * (first color ^ 2 / (centerLaw security).weight color) +
        2 * (second color ^ 2 / (centerLaw security).weight color) := by
    have hscalar : (first color - second color) ^ 2 ≤ 2 * first color ^ 2 + 2 * second color ^ 2 := by
      nlinarith [sq_nonneg (first color + second color)]
    exact (div_le_div_of_nonneg_right hscalar ((centerLaw security).nonneg color)).trans_eq (by ring)
  simpa only [profileSquareNorm, Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum] using
    Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)

theorem bodyCertificateDensity_square_bound (security : ℕ) :
    (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) ≤
      compensation security ^ 2 * (4 + 512 / activation security) := by
  have hdensity : (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) =
      profileSquareNorm (centerLaw security).weight (bodyCertificateProfile security) := densityScore_square _ _
  rw [hdensity, bodyCertificateProfile_formula, profileSquareNorm_smul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (compensation security))
  have h := center_profile_sub_square_le_two security (safeLaw security).weight (anchorPrimaryMean security)
  have hs := safeLaw_center_square_le_two security
  have ha := anchorPrimaryMean_center_square_le security
  calc
    _ ≤ 2 * profileSquareNorm (centerLaw security).weight (safeLaw security).weight +
        2 * profileSquareNorm (centerLaw security).weight (anchorPrimaryMean security) := h
    _ ≤ 2 * 2 + 2 * (256 / activation security) :=
      add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num)) (mul_le_mul_of_nonneg_left ha (by norm_num))
    _ = _ := by ring

theorem bodyCertificateDensity_square_decay (security : ℕ) :
    (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) ≤
      4096 / (Parameters.base security : ℝ) ^ 62 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  have hc := pow_le_pow_left₀ (compensation_nonneg security) (compensation_decay security) 2
  have hfactor : 4 + 512 / activation security ≤ 4096 * (Parameters.base security : ℝ) ^ 2 := by
    have hinv := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security)
      (show (0 : ℝ) ≤ 512 by norm_num)
    calc
      _ = 4 + 512 * (1 / activation security) := by ring
      _ ≤ 4 + 512 * (4 * (Parameters.base security : ℝ)) := add_le_add le_rfl hinv
      _ ≤ _ := by nlinarith only [hb1, sq_nonneg ((Parameters.base security : ℝ) - 1)]
  have hfactor0 : 0 ≤ 4 + 512 / activation security := by have := activation_pos security; positivity
  calc
    _ ≤ compensation security ^ 2 * (4 + 512 / activation security) := bodyCertificateDensity_square_bound security
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 32) ^ 2 * (4096 * (Parameters.base security : ℝ) ^ 2) :=
      mul_le_mul hc hfactor hfactor0 (sq_nonneg _)
    _ = _ := by field_simp

theorem bodyCertificateDensity_norm_decay (security : ℕ) :
    Real.sqrt (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) ≤
      64 / (Parameters.base security : ℝ) ^ 31 := by
  have hb := FirstResponse.base_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hden : (64 / (Parameters.base security : ℝ) ^ 31) ^ 2 =
      4096 / (Parameters.base security : ℝ) ^ 62 := by ring
  rw [hden]
  exact bodyCertificateDensity_square_decay security

/-- Root-marginal convolution is the actual mixture of cyclic palette
equivalences induced by the independent protected edge difference. -/
def rootConvolutionProfile (security : ℕ) (profile : Palette security → ℝ) : Palette security → ℝ :=
  fun output => ∑ seed, (actualSeedLaw security).weight seed *
    profile ((shiftEquiv security (actualBlur security seed)).symm output)

def convolvedCenterLaw (security : ℕ) : FiniteDist (Palette security) :=
  (actualSeedLaw security).mix (fun seed => (centerLaw security).map
    (shiftEquiv security (actualBlur security seed)))

def bodyLeadingResponse (security : ℕ) (density : Palette security → ℝ) : Palette security → ℝ :=
  rootConvolutionProfile security (fun center => (centerLaw security).weight center * density center)

theorem bodyLaw_false_weight (security : ℕ) (output : Palette security) :
    (bodyLaw security false).weight output = rootConvolutionProfile security (safeLaw security).weight output := by
  simp only [bodyLaw, FiniteDist.mix_weight, FiniteDist.map_equiv_weight,
    Bool.false_eq_true, if_false, add_zero, rootConvolutionProfile]

theorem convolvedCenterLaw_weight (security : ℕ) (output : Palette security) :
    (convolvedCenterLaw security).weight output = rootConvolutionProfile security (centerLaw security).weight output := by
  simp only [convolvedCenterLaw, FiniteDist.mix_weight, FiniteDist.map_equiv_weight, rootConvolutionProfile]

theorem bodyCertificateDensity_leading (security : ℕ) :
    bodyLeadingResponse security (bodyCertificateDensity security) =
      (convolvedCenterLaw security).weight - (bodyLaw security false).weight := by
  rw [bodyLeadingResponse, bodyCertificateDensity_profile]
  funext output
  rw [Pi.sub_apply, convolvedCenterLaw_weight, bodyLaw_false_weight]
  simp only [rootConvolutionProfile, bodyCertificateProfile, mul_sub, Finset.sum_sub_distrib]

/-- The two actual canonical atoms form the complete free-body leading
certificate: the current root-convolved center law minus uniformity. -/
theorem free_background_certificate_leading (security : ℕ) :
    activation security • FirstResponse.response security
      (fun color => (primaryLaw security).weight color * primaryCertificateDensity security color) +
      bodyLeadingResponse security (bodyCertificateDensity security) =
        (convolvedCenterLaw security).weight - uniformProfile security := by
  rw [primaryCertificateDensity_leading, bodyCertificateDensity_leading]
  funext output
  simp only [Pi.add_apply, Pi.sub_apply, bodyDeviation]
  ring

/-- The primary certificate also has a concrete stable physical paired
score under the actual independent two-control reference. -/
theorem primaryCertificate_paired_energy_decay (security : ℕ) :
    (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
      PairedResponse.pairedScore security (primaryCertificateDensity security) primary center ^ 2) ≤
        49536 / (Parameters.base security : ℝ) ^ 92 := by
  calc
    _ ≤ 129 * ∑ primary, (primaryLaw security).weight primary * primaryCertificateDensity security primary ^ 2 :=
      PairedResponse.pairedScore_energy_le security _ (primaryCertificateDensity_centered security)
    _ ≤ 129 * (384 / (Parameters.base security : ℝ) ^ 92) :=
      mul_le_mul_of_nonneg_left (primaryCertificateDensity_square_decay security) (by norm_num)
    _ = _ := by ring

end

end CurrentAFT.BackgroundCertificates

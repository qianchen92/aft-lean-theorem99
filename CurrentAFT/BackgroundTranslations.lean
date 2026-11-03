import CurrentAFT.BackgroundCertificates

/-!
# Actual cyclic translation certificates for the shared queue

A translated safe law is projected back to the safe palette by returning
its unsafe mass according to the original safe law. Both parts are finite
explicit sums. The body certificate records the projected difference;
the remaining root-convolved residual is lifted through the actual first
response inverse. Their leading responses reconstruct the full translated
safe profile minus uniformity exactly.

The bounds here are uniform over every cyclic translation. This weaker
body-seed estimate avoids a shift-size assumption and is sufficient after
the current population and radius weights are applied.
-/

namespace CurrentAFT.BackgroundTranslations

open AFT DiffuseProfiles ProposalPrimary FringeCertificate BackgroundCertificates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.bodySize
  Parameters.legCount Parameters.safeMargin DiffuseProfiles.activation DiffuseProfiles.actualSeedLaw
  primaryProfile safeLaw bodyLaw FirstResponse.responseEquiv

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

def shiftedSafeLaw (security : ℕ) (shift : ℤ) : FiniteDist (Palette security) :=
  (safeLaw security).map (shiftEquiv security shift)

theorem shiftedSafeLaw_height (security : ℕ) (shift : ℤ) (color : Palette security) :
    (shiftedSafeLaw security shift).weight color ≤ safeHeight security := by
  rw [shiftedSafeLaw, FiniteDist.map_equiv_weight]
  exact safeLaw_upper security _

def unsafePart (security : ℕ) (shift : ℤ) (color : Palette security) : ℝ :=
  if InwardAnchor.SafeColor security color then 0 else (shiftedSafeLaw security shift).weight color

def unsafeMass (security : ℕ) (shift : ℤ) : ℝ := ∑ color, unsafePart security shift color

theorem unsafePart_nonneg (security : ℕ) (shift : ℤ) (color : Palette security) :
    0 ≤ unsafePart security shift color := by
  unfold unsafePart
  split_ifs
  · rfl
  · exact FiniteDist.nonneg _ _

theorem unsafeMass_nonneg (security : ℕ) (shift : ℤ) : 0 ≤ unsafeMass security shift :=
  Finset.sum_nonneg (fun color _ => unsafePart_nonneg security shift color)

theorem unsafePart_le_shifted (security : ℕ) (shift : ℤ) (color : Palette security) :
    unsafePart security shift color ≤ (shiftedSafeLaw security shift).weight color := by
  unfold unsafePart
  split_ifs
  · exact FiniteDist.nonneg _ _
  · rfl

theorem unsafeMass_le_one (security : ℕ) (shift : ℤ) : unsafeMass security shift ≤ 1 := by
  calc
    _ ≤ ∑ color, (shiftedSafeLaw security shift).weight color :=
      Finset.sum_le_sum (fun color _ => unsafePart_le_shifted security shift color)
    _ = 1 := FiniteDist.sum_one _

theorem unsafePart_le_hole (security : ℕ) (shift : ℤ) (color : Palette security) :
    unsafePart security shift color ≤ safeHeight security - (safeLaw security).weight color := by
  by_cases hsafe : InwardAnchor.SafeColor security color
  · simp only [unsafePart, if_pos hsafe, safeLaw_weight, sub_self, le_refl]
  · simp only [unsafePart, if_neg hsafe, safeLaw_weight, sub_zero]
    exact shiftedSafeLaw_height security shift color

theorem unsafeMass_le_fringeMass (security : ℕ) (shift : ℤ) :
    unsafeMass security shift ≤ fringeMass security := by
  calc
    _ ≤ ∑ color, (safeHeight security - (safeLaw security).weight color) :=
      Finset.sum_le_sum (fun color _ => unsafePart_le_hole security shift color)
    _ = fringeMass security := by
      rw [fringeMass_height]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, FiniteDist.sum_one]

/-- This is the actual safe projection, including its returned unsafe mass. -/
def projectedShiftProfile (security : ℕ) (shift : ℤ) (color : Palette security) : ℝ :=
  (shiftedSafeLaw security shift).weight color - unsafePart security shift color +
    unsafeMass security shift * (safeLaw security).weight color

theorem projectedShiftProfile_nonneg (security : ℕ) (shift : ℤ) (color : Palette security) :
    0 ≤ projectedShiftProfile security shift color := by
  unfold projectedShiftProfile
  exact add_nonneg (sub_nonneg.mpr (unsafePart_le_shifted security shift color))
    (mul_nonneg (unsafeMass_nonneg security shift) ((safeLaw security).nonneg color))

theorem projectedShiftProfile_mass (security : ℕ) (shift : ℤ) :
    ∑ color, projectedShiftProfile security shift color = 1 := by
  simp only [projectedShiftProfile, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, FiniteDist.sum_one, mul_one, unsafeMass]
  ring

def projectedShiftLaw (security : ℕ) (shift : ℤ) : FiniteDist (Palette security) where
  weight := projectedShiftProfile security shift
  nonneg := projectedShiftProfile_nonneg security shift
  sum_one := projectedShiftProfile_mass security shift

theorem projectedShiftProfile_zero_outside (security : ℕ) (shift : ℤ) (color : Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security color) : projectedShiftProfile security shift color = 0 := by
  simp only [projectedShiftProfile, unsafePart, if_neg hunsafe, safeLaw_weight,
    sub_self, mul_zero, add_zero]

theorem projectedShiftProfile_majorant (security : ℕ) (shift : ℤ) (color : Palette security) :
    projectedShiftProfile security shift color ≤ 4 * (centerLaw security).weight color := by
  by_cases hsafe : InwardAnchor.SafeColor security color
  · have hheight := shiftedSafeLaw_height security shift color
    have hmass := unsafeMass_le_one security shift
    have hsafeLower := (centerProfile_bounds security color).1
    rw [safeLaw_weight, if_pos hsafe] at hsafeLower
    have hproject : projectedShiftProfile security shift color ≤ 2 * safeHeight security := by
      simp only [projectedShiftProfile, unsafePart, if_pos hsafe, sub_zero, safeLaw_weight]
      nlinarith only [hheight, mul_le_mul_of_nonneg_right hmass (safeHeight_pos security).le]
    change _ ≤ 4 * centerProfile security color
    linarith
  · rw [projectedShiftProfile_zero_outside security shift color hsafe]
    exact mul_nonneg (by norm_num) ((centerLaw security).nonneg color)

def safeSeedProfile (security : ℕ) (shift : ℤ) : Palette security → ℝ :=
  fun color => projectedShiftProfile security shift color - (safeLaw security).weight color

def safeSeedDensity (security : ℕ) (shift : ℤ) (color : Palette security) : ℝ :=
  safeSeedProfile security shift color / (centerLaw security).weight color

theorem safeSeedProfile_mass (security : ℕ) (shift : ℤ) : ∑ color, safeSeedProfile security shift color = 0 := by
  simp only [safeSeedProfile, Finset.sum_sub_distrib, projectedShiftProfile_mass, FiniteDist.sum_one, sub_self]

theorem safeSeedProfile_zero_outside (security : ℕ) (shift : ℤ) (color : Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security color) : safeSeedProfile security shift color = 0 := by
  simp only [safeSeedProfile, projectedShiftProfile_zero_outside security shift color hunsafe,
    safeLaw_weight, if_neg hunsafe, sub_self]

theorem safeSeedDensity_profile (security : ℕ) (shift : ℤ) :
    (fun color => (centerLaw security).weight color * safeSeedDensity security shift color) =
      safeSeedProfile security shift := by
  funext color
  by_cases hz : (centerLaw security).weight color = 0
  · have hproject : projectedShiftProfile security shift color = 0 := by
      have h := projectedShiftProfile_majorant security shift color
      rw [hz, mul_zero] at h
      exact le_antisymm h (projectedShiftProfile_nonneg security shift color)
    have hsafe : (safeLaw security).weight color = 0 := by
      have h := (centerProfile_bounds security color).1
      change (safeLaw security).weight color / 2 ≤ (centerLaw security).weight color at h
      rw [hz] at h
      linarith [(safeLaw security).nonneg color]
    simp only [hz, zero_mul, safeSeedProfile, hproject, hsafe, sub_self]
  · unfold safeSeedDensity
    field_simp

theorem safeSeedDensity_centered (security : ℕ) (shift : ℤ) :
    (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color) = 0 := by
  rw [safeSeedDensity_profile]
  exact safeSeedProfile_mass security shift

theorem safeSeedDensity_zero_outside (security : ℕ) (shift : ℤ) (color : Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security color) : safeSeedDensity security shift color = 0 := by
  simp only [safeSeedDensity, safeSeedProfile_zero_outside security shift color hunsafe, zero_div]

theorem safeSeedDensity_square_le (security : ℕ) (shift : ℤ) :
    (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color ^ 2) ≤ 12 := by
  have hproject : profileSquareNorm (centerLaw security).weight (projectedShiftProfile security shift) ≤ 4 := by
    simpa only [projectedShiftProfile_mass, mul_one] using dominated_profile_square_le security
      (centerLaw security).weight (projectedShiftProfile security shift) 4 (by norm_num)
      (centerLaw security).nonneg (projectedShiftProfile_nonneg security shift)
      (projectedShiftProfile_majorant security shift)
  have hdensity : (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color ^ 2) =
      profileSquareNorm (centerLaw security).weight (safeSeedProfile security shift) := densityScore_square _ _
  rw [hdensity]
  have h := center_profile_sub_square_le_two security (projectedShiftProfile security shift) (safeLaw security).weight
  change profileSquareNorm (centerLaw security).weight (projectedShiftProfile security shift - (safeLaw security).weight) ≤ _
  linarith [safeLaw_center_square_le_two security]

theorem safeSeedDensity_norm_le_four (security : ℕ) (shift : ℤ) :
    Real.sqrt (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color ^ 2) ≤ 4 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · linarith [safeSeedDensity_square_le security shift]

theorem rootConvolutionProfile_nonneg (security : ℕ) (profile : Palette security → ℝ)
    (hprofile : ∀ color, 0 ≤ profile color) (output : Palette security) :
    0 ≤ rootConvolutionProfile security profile output :=
  Finset.sum_nonneg (fun seed _ => mul_nonneg ((actualSeedLaw security).nonneg seed) (hprofile _))

theorem rootConvolutionProfile_mono (security : ℕ) (first second : Palette security → ℝ)
    (hle : ∀ color, first color ≤ second color) (output : Palette security) :
    rootConvolutionProfile security first output ≤ rootConvolutionProfile security second output :=
  Finset.sum_le_sum (fun seed _ => mul_le_mul_of_nonneg_left (hle _) ((actualSeedLaw security).nonneg seed))

theorem rootConvolutionProfile_mass (security : ℕ) (profile : Palette security → ℝ) :
    (∑ output, rootConvolutionProfile security profile output) = ∑ color, profile color := by
  unfold rootConvolutionProfile
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (shiftEquiv security _).symm.sum_comp profile]
  rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem convolved_hole_eq_fringe (security : ℕ) (output : Palette security) :
    rootConvolutionProfile security (fun color => safeHeight security - (safeLaw security).weight color) output =
      fringe security output := by
  simp only [rootConvolutionProfile, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    FiniteDist.sum_one, one_mul, fringe, bodyLaw_false_weight]

theorem convolved_unsafe_le_fringe (security : ℕ) (shift : ℤ) (output : Palette security) :
    rootConvolutionProfile security (unsafePart security shift) output ≤ fringe security output := by
  exact (rootConvolutionProfile_mono security _ _ (unsafePart_le_hole security shift) output).trans_eq
    (convolved_hole_eq_fringe security output)

def translationResidual (security : ℕ) (shift : ℤ) : Palette security → ℝ :=
  fun output => rootConvolutionProfile security (unsafePart security shift) output -
    unsafeMass security shift * (bodyLaw security false).weight output

theorem translationResidual_mass (security : ℕ) (shift : ℤ) : ∑ output, translationResidual security shift output = 0 := by
  simp only [translationResidual, Finset.sum_sub_distrib, rootConvolutionProfile_mass,
    ← Finset.mul_sum, FiniteDist.sum_one, mul_one, unsafeMass, sub_self]

theorem convolvedUnsafe_square_bound (security : ℕ) (shift : ℤ) :
    profileSquareNorm (primaryLaw security).weight (rootConvolutionProfile security (unsafePart security shift)) ≤
      compensation security * unsafeMass security shift := by
  have hq := FirstResponse.modulus_pos security
  have hp (color : Palette security) : 0 < (primaryLaw security).weight color :=
    (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (primaryProfile_atom_lower security color)
  have hnonneg := rootConvolutionProfile_nonneg security _ (unsafePart_nonneg security shift)
  have hdom (color : Palette security) :
      |rootConvolutionProfile security (unsafePart security shift) color| ≤
        compensation security * (primaryLaw security).weight color := by
    rw [abs_of_nonneg (hnonneg color)]
    exact (convolved_unsafe_le_fringe security shift color).trans (fringe_majorant security color)
  have h := signProfile_square_bound _ _ _ hp hdom
  simpa only [abs_of_nonneg (hnonneg _), rootConvolutionProfile_mass, unsafeMass] using h

theorem bodyLaw_false_primary_square_le_four (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (bodyLaw security false).weight ≤ 4 := by
  have hq := FirstResponse.modulus_pos security
  have hheight : safeHeight security ≤ 2 / (Parameters.modulus security : ℝ) := by
    have hstrip : 4 * (Parameters.safeMargin security : ℝ) < Parameters.modulus security := by
      exact_mod_cast safe_clearance security
    unfold safeHeight
    calc
      _ ≤ 1 / ((Parameters.modulus security : ℝ) / 2) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = _ := by ring
  have hdom (color : Palette security) : (bodyLaw security false).weight color ≤
      4 * (primaryLaw security).weight color := by
    have hp := mul_le_mul_of_nonneg_left (primaryProfile_atom_lower security color)
      (show (0 : ℝ) ≤ 4 by norm_num)
    have heq : 4 * (1 / (2 * (Parameters.modulus security : ℝ))) = 2 / Parameters.modulus security := by ring
    rw [heq] at hp
    exact ((bodyLaw_upper security false color).trans hheight).trans hp
  simpa only [FiniteDist.sum_one, mul_one] using dominated_profile_square_le security
    (primaryLaw security).weight (bodyLaw security false).weight 4 (by norm_num)
    (primaryLaw security).nonneg (bodyLaw security false).nonneg hdom

theorem translationResidual_square_bound (security : ℕ) (shift : ℤ) :
    profileSquareNorm (primaryLaw security).weight (translationResidual security shift) ≤
      2 * compensation security * unsafeMass security shift + 8 * unsafeMass security shift ^ 2 := by
  have h := FringeCertificate.profileSquareNorm_sub_le_two security
    (rootConvolutionProfile security (unsafePart security shift))
    (unsafeMass security shift • (bodyLaw security false).weight)
  rw [profileSquareNorm_smul] at h
  have hunsafe := convolvedUnsafe_square_bound security shift
  have hbody := mul_le_mul_of_nonneg_left (bodyLaw_false_primary_square_le_four security)
    (sq_nonneg (unsafeMass security shift))
  change profileSquareNorm (primaryLaw security).weight
    (rootConvolutionProfile security (unsafePart security shift) - unsafeMass security shift •
      (bodyLaw security false).weight) ≤ _
  nlinarith only [h, hunsafe, hbody]

def residualCertificateProfile (security : ℕ) (shift : ℤ) : Palette security → ℝ :=
  (activation security)⁻¹ • (FirstResponse.responseEquiv security).symm (translationResidual security shift)

def residualCertificateDensity (security : ℕ) (shift : ℤ) (color : Palette security) : ℝ :=
  residualCertificateProfile security shift color / (primaryLaw security).weight color

theorem residualCertificateDensity_profile (security : ℕ) (shift : ℤ) :
    (fun color => (primaryLaw security).weight color * residualCertificateDensity security shift color) =
      residualCertificateProfile security shift := by
  have hq := FirstResponse.modulus_pos security
  funext color
  have hp : (primaryLaw security).weight color ≠ 0 := ne_of_gt
    ((by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (primaryProfile_atom_lower security color))
  unfold residualCertificateDensity
  field_simp

theorem residualCertificateDensity_centered (security : ℕ) (shift : ℤ) :
    (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color) = 0 := by
  rw [residualCertificateDensity_profile]
  simp only [residualCertificateProfile, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    FirstResponse.response_inverse_preserves_mass, translationResidual_mass, mul_zero]

theorem residualCertificateDensity_leading (security : ℕ) (shift : ℤ) :
    activation security • FirstResponse.response security
      (fun color => (primaryLaw security).weight color * residualCertificateDensity security shift color) =
        translationResidual security shift := by
  rw [residualCertificateDensity_profile, residualCertificateProfile, map_smul]
  have hinverse : FirstResponse.response security
      ((FirstResponse.responseEquiv security).symm (translationResidual security shift)) = translationResidual security shift := by
    rw [← FirstResponse.responseEquiv_forward]
    exact (FirstResponse.responseEquiv security).apply_symm_apply _
  rw [hinverse, smul_smul, mul_inv_cancel₀ (activation_pos security).ne', one_smul]

theorem translationResidual_square_decay (security : ℕ) (shift : ℤ) :
    profileSquareNorm (primaryLaw security).weight (translationResidual security shift) ≤
      12 / (Parameters.base security : ℝ) ^ 94 := by
  have hmass := unsafeMass_le_fringeMass security shift
  have hmassSq := pow_le_pow_left₀ (unsafeMass_nonneg security shift) hmass 2
  have hproduct := mul_le_mul_of_nonneg_left hmass (compensation_nonneg security)
  have hproduct0 := mul_nonneg (compensation_nonneg security) (fringeMass_nonneg security)
  calc
    _ ≤ 2 * compensation security * unsafeMass security shift + 8 * unsafeMass security shift ^ 2 :=
      translationResidual_square_bound security shift
    _ ≤ 2 * (compensation security * fringeMass security) + 8 * fringeMass security ^ 2 := by
      have h := add_le_add (mul_le_mul_of_nonneg_left hproduct (show (0 : ℝ) ≤ 2 by norm_num))
        (mul_le_mul_of_nonneg_left hmassSq (show (0 : ℝ) ≤ 8 by norm_num))
      exact (by ring_nf at h ⊢; exact h)
    _ ≤ 2 * (4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security) := by
      nlinarith only [hproduct0]
    _ ≤ 2 * (6 / (Parameters.base security : ℝ) ^ 94) :=
      mul_le_mul_of_nonneg_left (bodyDeviation_budget_decay security) (by norm_num)
    _ = _ := by ring

theorem residualCertificateDensity_square_decay (security : ℕ) (shift : ℤ) :
    (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2) ≤
      768 / (Parameters.base security : ℝ) ^ 92 := by
  have hb := FirstResponse.base_pos security
  have hpositive (profile : Palette security → ℝ) : 0 ≤ profileSquareNorm (primaryLaw security).weight profile :=
    profileSquareNorm_nonneg _ _ (primaryLaw security).nonneg
  have hinverse := (actual_first_response_stable security (translationResidual security shift)).2
  have hinverseSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hinverse 2
  rw [mul_pow, Real.sq_sqrt (hpositive _), Real.sq_sqrt (hpositive _)] at hinverseSq
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hinverseSq
  have hnorm : (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2) =
      (activation security)⁻¹ ^ 2 * profileSquareNorm (primaryLaw security).weight
        ((FirstResponse.responseEquiv security).symm (translationResidual security shift)) := by
    rw [show (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2) =
        profileSquareNorm (primaryLaw security).weight (residualCertificateProfile security shift) from densityScore_square _ _]
    rw [residualCertificateProfile, profileSquareNorm_smul]
  rw [hnorm]
  have hinv := FirstResponse.activation_inverse_le security
  have hinvsq := pow_le_pow_left₀ (one_div_pos.mpr (activation_pos security)).le hinv 2
  have hscale : (activation security)⁻¹ ^ 2 ≤ 16 * (Parameters.base security : ℝ) ^ 2 := by
    simpa only [one_div, mul_pow, show (4 : ℝ) ^ 2 = 16 by norm_num] using hinvsq
  calc
    _ ≤ (16 * (Parameters.base security : ℝ) ^ 2) *
        (4 * (12 / (Parameters.base security : ℝ) ^ 94)) :=
      mul_le_mul hscale (hinverseSq.trans (mul_le_mul_of_nonneg_left
        (translationResidual_square_decay security shift) (by norm_num)))
        (hpositive _) (by positivity)
    _ = _ := by field_simp; ring

theorem residualCertificateDensity_norm_decay (security : ℕ) (shift : ℤ) :
    Real.sqrt (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2) ≤
      32 / (Parameters.base security : ℝ) ^ 46 := by
  have hb := FirstResponse.base_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hden : (32 / (Parameters.base security : ℝ) ^ 46) ^ 2 =
      1024 / (Parameters.base security : ℝ) ^ 92 := by ring
  rw [hden]
  exact (residualCertificateDensity_square_decay security shift).trans
    (div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hb.le _))

/-- Both pieces are explicit public coefficients indexed by the same
queue shift; summing their evaluated profiles gives its actual factor. -/
theorem translation_certificate_leading (security : ℕ) (shift : ℤ) :
    activation security • FirstResponse.response security
      (fun color => (primaryLaw security).weight color * primaryCertificateDensity security color) +
    bodyLeadingResponse security (safeSeedDensity security shift) +
    activation security • FirstResponse.response security
      (fun color => (primaryLaw security).weight color * residualCertificateDensity security shift color) =
      rootConvolutionProfile security (shiftedSafeLaw security shift).weight - uniformProfile security := by
  rw [primaryCertificateDensity_leading, residualCertificateDensity_leading,
    bodyLeadingResponse, safeSeedDensity_profile]
  funext output
  rw [Pi.add_apply, Pi.add_apply, Pi.sub_apply]
  simp only [bodyDeviation, translationResidual, rootConvolutionProfile, safeSeedProfile, projectedShiftProfile,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    mul_left_comm, bodyLaw_false_weight]
  ring

end

end CurrentAFT.BackgroundTranslations

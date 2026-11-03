import CurrentAFT.DiffuseProfiles
import AFT.FinitePrimaryInverse

/-!
# The actual current rank-one first response

The sign profile and activation in this file are the actual trimmed-slice
diffuse profiles and clipped Gaussian zero atom of `DiffuseProfiles`.
The elementary estimates for these concrete distributions, together with
the current public sizes, imply the perturbation and inverse bounds.

The reference primary law only supplies its normalized mass and the
elementary lower atom bound. No response norm or inverse is assumed.
The weighted norm is stated as its genuine finite square sum, without
introducing a potentially incompatible norm instance on the palette.
The physical paired-channel factorization is a separate obligation.
-/

namespace CurrentAFT.FirstResponse

open AFT DiffuseProfiles
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff DiffuseProfiles.actualProfile DiffuseProfiles.signProfile
  DiffuseProfiles.activation DiffuseProfiles.actualSeedLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

/-- Comparison with the exact palette midpoint, using doubled integer
coordinates so no division or rounding convention is implicit. -/
def anchorSign (security : ℕ) (color : Palette security) : ℝ :=
  if 2 * color.val < Parameters.modulus security - 1 then -1
  else if Parameters.modulus security - 1 < 2 * color.val then 1 else 0

theorem anchorSign_abs_le_one (security : ℕ) (color : Palette security) :
    |anchorSign security color| ≤ 1 := by
  unfold anchorSign
  split_ifs <;> norm_num

theorem modulus_pos (security : ℕ) : (0 : ℝ) < Parameters.modulus security := by
  exact_mod_cast (Parameters.modulus_spec security).2.pos

theorem base_pos (security : ℕ) : (0 : ℝ) < Parameters.base security := by
  exact_mod_cast Parameters.base_pos security

/-- A direct bound on the actual deletion length, using the current
anchor width `base^48` and source cutoff `base^2`. -/
theorem deletion_le_six_anchor (security : ℕ) :
    deletion security ≤ 6 * Parameters.base security ^ 48 := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hconstant : 1 ≤ Parameters.base security ^ 48 := one_le_pow₀ hb
  have hcutoff : Parameters.base security ^ 2 ≤ Parameters.base security ^ 48 :=
    Nat.pow_le_pow_right hb (by omega)
  simp only [deletion, anchorWidth_eq, Parameters.sourceCutoff]
  omega

/-- This quantitative budget comes from the actual modulus lower bound;
it is stronger than the smallness needed for a stable first inverse. -/
theorem deletion_budget (security : ℕ) :
    256 * deletion security * Parameters.base security ^ 12 ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  calc
    _ ≤ 256 * (6 * Parameters.base security ^ 48) * Parameters.base security ^ 12 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (deletion_le_six_anchor security))
    _ = 1536 * (Parameters.base security ^ 48 * Parameters.base security ^ 12) := by ring
    _ = 1536 * Parameters.base security ^ 60 := by rw [← pow_add]
    _ ≤ 65536 * Parameters.base security ^ 64 :=
      Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right hb (by omega))
    _ ≤ _ := (Parameters.modulus_bounds security).1

theorem two_deletion_le_modulus (security : ℕ) :
    2 * deletion security ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hpower : 1 ≤ Parameters.base security ^ 12 := one_le_pow₀ hb
  calc
    2 * deletion security ≤ (256 * deletion security) * Parameters.base security ^ 12 :=
      (by omega : 2 * deletion security ≤ 256 * deletion security).trans
        (Nat.le_mul_of_pos_right _ (by omega))
    _ ≤ _ := deletion_budget security

/-- A simpler consequence useful for the proposal's pointwise losses. -/
theorem deletion_linear_budget (security : ℕ) :
    64 * deletion security * Parameters.base security ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hpower : Parameters.base security ≤ Parameters.base security ^ 12 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (show 1 ≤ 12 by omega)
  exact (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num : 64 ≤ 256)) hpower).trans
    (deletion_budget security)

/-- The current clipped Gaussian activation has the elementary inverse
scale `4*base`; this is derived from its actual zero-atom estimate. -/
theorem activation_lower_simple (security : ℕ) :
    1 / (4 * (Parameters.base security : ℝ)) ≤ activation security := by
  have hb := base_pos security
  have hpi : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr Real.two_le_pi
  apply le_trans _ (activation_lower security)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem activation_inverse_le (security : ℕ) :
    1 / activation security ≤ 4 * (Parameters.base security : ℝ) := by
  have hb := base_pos security
  have h := one_div_le_one_div_of_le
    (by positivity : 0 < 1 / (4 * (Parameters.base security : ℝ))) (activation_lower_simple security)
  simpa only [one_div_one_div] using h

theorem signProfile_l1_le_half_activation (security : ℕ) :
    (∑ color, |signProfile security color|) ≤ activation security / 2 := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hpower : Parameters.base security ≤ Parameters.base security ^ 12 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (show 1 ≤ 12 by omega)
  have hbudgetNat : 32 * deletion security * Parameters.base security ≤ Parameters.modulus security :=
    (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num : 32 ≤ 256)) hpower).trans
      (deletion_budget security)
  have hbudget : 32 * (deletion security : ℝ) * Parameters.base security ≤ Parameters.modulus security := by
    exact_mod_cast hbudgetNat
  have hq := modulus_pos security
  have hb0 := base_pos security
  calc
    _ ≤ 4 * (deletion security : ℝ) / Parameters.modulus security := signProfile_l1 security
    _ ≤ 1 / (8 * (Parameters.base security : ℝ)) := by
      apply (div_le_div_iff₀ hq (by positivity)).mpr
      nlinarith only [hbudget]
    _ = (1 / (4 * (Parameters.base security : ℝ))) / 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (activation_lower_simple security) (by norm_num)

theorem signProfile_l1_lt_activation (security : ℕ) :
    (∑ color, |signProfile security color|) < activation security := by
  have h := signProfile_l1_le_half_activation security
  have ha := activation_pos security
  linarith

/-- The actual denominator in the printed rank-one inverse is positive,
with no supplied invertibility premise. -/
theorem inverse_denominator_lower (security : ℕ) :
    activation security / 2 ≤ activation security +
      signFunctional (anchorSign security) (signProfile security) :=
  primaryRank_denominator_lower _ _
    ((signFunctional_abs_le_l1 (anchorSign security) (signProfile security)
      (anchorSign_abs_le_one security)).trans (signProfile_l1_le_half_activation security))

theorem inverse_denominator_pos (security : ℕ) :
    0 < activation security + signFunctional (anchorSign security) (signProfile security) :=
  (half_pos (activation_pos security)).trans_le (inverse_denominator_lower security)

/-- This response uses the actual current diffuse profile, not an
uninterpreted perturbation parameter or the older V7 physical model. -/
def response (security : ℕ) : (Palette security → ℝ) →ₗ[ℝ] (Palette security → ℝ) :=
  primaryRankOperator (activation security) (signProfile security) (profileSignMap (anchorSign security))

def responseEquiv (security : ℕ) : (Palette security → ℝ) ≃ₗ[ℝ] (Palette security → ℝ) :=
  finitePrimaryRankEquiv (activation security) (signProfile security) (anchorSign security)
    (anchorSign_abs_le_one security) (signProfile_l1_lt_activation security)

theorem responseEquiv_forward (security : ℕ) (profile : Palette security → ℝ) :
    responseEquiv security profile = response security profile := rfl

theorem response_inverse_formula (security : ℕ) (profile : Palette security → ℝ) :
    (responseEquiv security).symm profile = profile -
      ((activation security + signFunctional (anchorSign security) (signProfile security))⁻¹ *
        signFunctional (anchorSign security) profile) • signProfile security :=
  finitePrimaryRankEquiv_inverse_apply _ _ _ _ _ _

theorem response_preserves_mass (security : ℕ) (profile : Palette security → ℝ) :
    (∑ color, response security profile color) = ∑ color, profile color := by
  simp only [response, primaryRankOperator_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, signProfile_mass, mul_zero, add_zero]

theorem response_inverse_preserves_mass (security : ℕ) (profile : Palette security → ℝ) :
    (∑ color, (responseEquiv security).symm profile color) = ∑ color, profile color := by
  have h := response_preserves_mass security ((responseEquiv security).symm profile)
  have hresponse : response security ((responseEquiv security).symm profile) = profile :=
    (responseEquiv security).apply_symm_apply profile
  rw [hresponse] at h
  exact h.symm

theorem signProfile_majorant (security : ℕ) (primary : Palette security → ℝ)
    (hprimary : ∀ color, 1 / (2 * (Parameters.modulus security : ℝ)) ≤ primary color)
    (color : Palette security) : |signProfile security color| ≤ 4 * primary color := by
  have hq := modulus_pos security
  have hdelete : 2 * (deletion security : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast two_deletion_le_modulus security
  calc
    _ ≤ 1 / ((Parameters.modulus security : ℝ) - deletion security) := signProfile_upper security color
    _ ≤ 1 / ((Parameters.modulus security : ℝ) / 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = 4 * (1 / (2 * (Parameters.modulus security : ℝ))) := by field_simp; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (hprimary color) (by norm_num)

private theorem actual_correction_coefficient_le (security : ℕ) :
    4 * (∑ color, |signProfile security color|) / activation security ^ 2 ≤
      1 / (Parameters.base security : ℝ) ^ 10 := by
  have hq := modulus_pos security
  have hb := base_pos security
  have hsum0 : 0 ≤ ∑ color, |signProfile security color| := Finset.sum_nonneg (fun color _ => abs_nonneg _)
  have hinv := activation_inverse_le security
  have hinv0 : 0 ≤ 1 / activation security := (one_div_pos.mpr (activation_pos security)).le
  have hinvsq : (1 / activation security) ^ 2 ≤ (4 * (Parameters.base security : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hinv0 hinv _
  have hsum := mul_le_mul_of_nonneg_left (signProfile_l1 security) (by norm_num : (0 : ℝ) ≤ 4)
  have hbudget : 256 * (deletion security : ℝ) * (Parameters.base security : ℝ) ^ 12 ≤
      Parameters.modulus security := by exact_mod_cast deletion_budget security
  calc
    _ = (4 * ∑ color, |signProfile security color|) * (1 / activation security) ^ 2 := by ring
    _ ≤ (16 * (deletion security : ℝ) / Parameters.modulus security) *
        (4 * (Parameters.base security : ℝ)) ^ 2 := by
      apply mul_le_mul _ hinvsq (sq_nonneg _) (by positivity)
      exact hsum.trans_eq (by ring)
    _ = (256 * (deletion security : ℝ) * (Parameters.base security : ℝ) ^ 2) /
        Parameters.modulus security := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hq (pow_pos hb _)).mpr
      nlinarith only [hbudget]

/-- The concrete first response has squared perturbation at most
`base^-10` in every normalized reference with the stated atom bound. -/
theorem response_defect_square_le (security : ℕ) (primary : Palette security → ℝ)
    (hprimary : ∀ color, 1 / (2 * (Parameters.modulus security : ℝ)) ≤ primary color)
    (hmass : ∑ color, primary color = 1) (profile : Palette security → ℝ) :
    profileSquareNorm primary (response security profile - profile) ≤
      (1 / (Parameters.base security : ℝ) ^ 10) * profileSquareNorm primary profile := by
  have hq := modulus_pos security
  have hp (color) : 0 < primary color := (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le (hprimary color)
  have hdifference : response security profile - profile =
      (signFunctional (anchorSign security) profile / activation security) • signProfile security := by
    change primaryRankOperator (activation security) (signProfile security)
      (profileSignMap (anchorSign security)) profile - profile = _
    rw [primaryRankOperator_apply]
    change profile + ((activation security)⁻¹ * signFunctional (anchorSign security) profile) •
      signProfile security - profile = _
    rw [show (activation security)⁻¹ * signFunctional (anchorSign security) profile =
      signFunctional (anchorSign security) profile / activation security by ring]
    abel
  rw [hdifference]
  exact (rankCorrection_profileSquareNorm_le primary (signProfile security) (anchorSign security) profile
    (activation security) 4 hp hmass (anchorSign_abs_le_one security) (by norm_num)
    (signProfile_majorant security primary hprimary)).trans
      (mul_le_mul_of_nonneg_right (actual_correction_coefficient_le security)
        (profileSquareNorm_nonneg primary profile (fun color => (hp color).le)))

/-- The operator-norm statement written directly in its genuine
weighted profile norm: the defect is at most `base^-5`. -/
theorem response_defect_norm_le (security : ℕ) (primary : Palette security → ℝ)
    (hprimary : ∀ color, 1 / (2 * (Parameters.modulus security : ℝ)) ≤ primary color)
    (hmass : ∑ color, primary color = 1) (profile : Palette security → ℝ) :
    Real.sqrt (profileSquareNorm primary (response security profile - profile)) ≤
      Real.sqrt (profileSquareNorm primary profile) / (Parameters.base security : ℝ) ^ 5 := by
  have hq := modulus_pos security
  have hp (color) : 0 < primary color := (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le (hprimary color)
  have hn := profileSquareNorm_nonneg primary profile (fun color => (hp color).le)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [div_pow, Real.sq_sqrt hn, ← pow_mul]
  convert response_defect_square_le security primary hprimary hmass profile using 1
  ring

/-- The actual explicit inverse has norm at most two in the same
weighted profile norm, uniformly in the reference primary law. -/
theorem response_inverse_norm_le_two (security : ℕ) (primary : Palette security → ℝ)
    (hprimary : ∀ color, 1 / (2 * (Parameters.modulus security : ℝ)) ≤ primary color)
    (hmass : ∑ color, primary color = 1) (profile : Palette security → ℝ) :
    Real.sqrt (profileSquareNorm primary ((responseEquiv security).symm profile)) ≤
      2 * Real.sqrt (profileSquareNorm primary profile) := by
  have hq := modulus_pos security
  have hp (color) : 0 < primary color := (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le (hprimary color)
  let preimage := (responseEquiv security).symm profile
  have hresponse : response security preimage = profile := (responseEquiv security).apply_symm_apply profile
  have hdefect := response_defect_norm_le security primary hprimary hmass preimage
  have hb2 : (2 : ℝ) ≤ Parameters.base security := by exact_mod_cast Parameters.base_ge_two security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by linarith
  have hpower : (2 : ℝ) ≤ (Parameters.base security : ℝ) ^ 5 :=
    hb2.trans (by simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 5 by omega))
  have hdefectHalf :
      Real.sqrt (profileSquareNorm primary (response security preimage - preimage)) ≤
        Real.sqrt (profileSquareNorm primary preimage) / 2 :=
    hdefect.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) hpower)
  have hsplit : preimage = profile + -(response security preimage - preimage) := by rw [hresponse]; abel
  have htriangle := profileSquareNorm_sqrt_add_le primary profile
    (-(response security preimage - preimage)) hp
  rw [← hsplit] at htriangle
  have hnegative : profileSquareNorm primary (-(response security preimage - preimage)) =
      profileSquareNorm primary (response security preimage - preimage) := by
    simp only [profileSquareNorm, Pi.neg_apply, neg_sq]
  rw [hnegative] at htriangle
  change Real.sqrt (profileSquareNorm primary preimage) ≤ _
  linarith

end

end CurrentAFT.FirstResponse

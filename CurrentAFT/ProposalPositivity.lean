import CurrentAFT.ProposalPrimary

/-!
# Positivity of the actual current primary proposal

All scalar budgets are discharged from the fixed public sizes and the
actual clipped Gaussian activation. No positivity or small-response
certificate is supplied as a premise. This closes the primary atom bound
needed by the concrete first-response stability theorem.
-/

namespace CurrentAFT.ProposalPrimary

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
attribute [local irreducible] Parameters.base DiffuseProfiles.activation
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile

theorem safe_strip_budget (security : ℕ) :
    32 * Parameters.safeMargin security ≤ Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hp : Parameters.base security ^ 2 ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hq := (Parameters.modulus_bounds security).1
  simp only [Parameters.safeMargin, Parameters.sourceCutoff]
  omega

theorem body_deletion_budget (security : ℕ) :
    64 * Parameters.base security * Parameters.bodySize security *
      (2 * Parameters.safeMargin security) ≤
        Parameters.legCount security * Parameters.modulus security := by
  have hlarge : 384 ≤ Parameters.base security ^ 29 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 29
    norm_num at h
    omega
  have hpower : Parameters.base security * Parameters.base security ^ 96 *
      Parameters.base security ^ 2 = Parameters.base security ^ 99 := by
    calc
      _ = Parameters.base security ^ (1 + 96 + 2) := by simp only [pow_add, pow_one]
      _ = _ := rfl
  rw [Parameters.bodySize_eq, Parameters.legCount_eq, Parameters.safeMargin,
    Parameters.sourceCutoff]
  calc
    _ = 384 * Parameters.modulus security * (Parameters.base security *
        Parameters.base security ^ 96 * Parameters.base security ^ 2) := by ring
    _ = 384 * Parameters.modulus security * Parameters.base security ^ 99 := by rw [hpower]
    _ ≤ Parameters.base security ^ 29 * Parameters.modulus security *
        Parameters.base security ^ 99 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hlarge)
    _ = _ := by rw [show 128 = 99 + 29 by omega, pow_add]; ac_rfl

theorem mark_body_budget (security : ℕ) :
    16 * (Parameters.bodySize security : ℝ) * (2 * Parameters.safeMargin security) ≤
      markMass security * Parameters.modulus security := by
  have hb := FirstResponse.base_pos security
  have ha := (activation_pos security).le
  have hactivation : 1 ≤ (4 * (Parameters.base security : ℝ)) * activation security := by
    have h := (div_le_iff₀ (show 0 < 4 * (Parameters.base security : ℝ) by positivity)).mp
      (FirstResponse.activation_lower_simple security)
    simpa only [mul_comm] using h
  have hbudget : 64 * (Parameters.base security : ℝ) * Parameters.bodySize security *
      (2 * Parameters.safeMargin security) ≤
        (Parameters.legCount security : ℝ) * Parameters.modulus security := by
    exact_mod_cast body_deletion_budget security
  have hscaled : (4 * (Parameters.base security : ℝ)) *
      (16 * Parameters.bodySize security * (2 * Parameters.safeMargin security)) ≤
        (4 * Parameters.base security) * (markMass security * Parameters.modulus security) := by
    calc
      _ = 64 * (Parameters.base security : ℝ) * Parameters.bodySize security *
          (2 * Parameters.safeMargin security) := by ring
      _ ≤ (Parameters.legCount security : ℝ) * Parameters.modulus security := hbudget
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hactivation
          (show 0 ≤ (Parameters.legCount security : ℝ) * Parameters.modulus security by positivity)
        simpa only [one_mul, markMass, mul_assoc, mul_left_comm, mul_comm] using h
  by_contra hnot
  have hdiff : 0 < 16 * (Parameters.bodySize security : ℝ) * (2 * Parameters.safeMargin security) -
      markMass security * Parameters.modulus security := sub_pos.mpr (lt_of_not_ge hnot)
  have hpositive := mul_pos (show 0 < 4 * (Parameters.base security : ℝ) by positivity) hdiff
  nlinarith only [hscaled, hpositive]

theorem activated_deletion_budget (security : ℕ) :
    16 * (deletion security : ℝ) ≤ activation security * Parameters.modulus security := by
  have hactivation : 1 ≤ (4 * (Parameters.base security : ℝ)) * activation security := by
    have hb := FirstResponse.base_pos security
    have h := (div_le_iff₀ (show 0 < 4 * (Parameters.base security : ℝ) by positivity)).mp
      (FirstResponse.activation_lower_simple security)
    simpa only [mul_comm] using h
  have hbudget : 64 * (deletion security : ℝ) * Parameters.base security ≤
      Parameters.modulus security := by exact_mod_cast FirstResponse.deletion_linear_budget security
  calc
    _ ≤ 16 * (deletion security : ℝ) * (4 * Parameters.base security * activation security) := by
      nlinarith [mul_le_mul_of_nonneg_left hactivation (show 0 ≤ 16 * (deletion security : ℝ) by positivity)]
    _ = (64 * (deletion security : ℝ) * Parameters.base security) * activation security := by ring
    _ ≤ (Parameters.modulus security : ℝ) * activation security :=
      mul_le_mul_of_nonneg_right hbudget (activation_pos security).le
    _ = _ := by ring

/-- The two actual deletion contributions are each at most one quarter. -/
theorem baselineLoss_le_half (security : ℕ) : baselineLoss security ≤ 1 / 2 := by
  have hq := FirstResponse.modulus_pos security
  have hm := markMass_pos security
  have ha := activation_pos security
  have hs0 : 0 ≤ (2 * Parameters.safeMargin security : ℝ) := by positivity
  have hd0 : 0 ≤ (deletion security : ℝ) := by positivity
  have hstrip : 16 * (2 * Parameters.safeMargin security : ℝ) ≤ Parameters.modulus security := by
    have h := Nat.cast_le (α := ℝ).mpr (safe_strip_budget security)
    push_cast at h
    nlinarith
  have hsafe : 0 < (Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security := by
    linarith
  have hdiff : 0 < (Parameters.modulus security : ℝ) - deletion security :=
    sub_pos.mpr (Nat.cast_lt.mpr (deletion_clearance security))
  have hbody := mark_body_budget security
  have hscaledStrip := mul_le_mul_of_nonneg_left hstrip hm.le
  have hmarkq : 0 ≤ markMass security * (Parameters.modulus security : ℝ) := by positivity
  have hfirst : (((Parameters.bodySize security : ℝ) + markMass security) *
      (2 * Parameters.safeMargin security)) /
      (markMass security * ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)) ≤
        1 / 4 := by
    apply (div_le_iff₀ (mul_pos hm hsafe)).mpr
    nlinarith only [hbody, hscaledStrip, hmarkq]
  have hsecond : 2 * (1 - activation security) * deletion security /
      (activation security * ((Parameters.modulus security : ℝ) - deletion security)) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos ha hdiff)).mpr
    have hbudget := activated_deletion_budget security
    have hproduct := mul_nonneg ha.le hd0
    nlinarith only [hbudget, hproduct]
  unfold baselineLoss
  linarith

theorem primaryProfile_atom_lower (security : ℕ)
    (color : Fin (Parameters.modulus security)) :
    1 / (2 * (Parameters.modulus security : ℝ)) ≤ primaryProfile security color := by
  have hq := FirstResponse.modulus_pos security
  apply le_trans _ (primaryProfile_lower security color)
  have h := baselineLoss_le_half security
  apply (div_le_div_iff₀ (by positivity) hq).mpr
  nlinarith

/-- The actual primary law is a probability distribution, with no positivity
certificate or analytic smallness assumption passed to the definition. -/
def primaryLaw (security : ℕ) : FiniteDist (Fin (Parameters.modulus security)) where
  weight := primaryProfile security
  nonneg color := (show (0 : ℝ) ≤ 1 / (2 * (Parameters.modulus security : ℝ)) from by
    have := FirstResponse.modulus_pos security
    positivity).trans (primaryProfile_atom_lower security color)
  sum_one := primaryProfile_mass security

/-- Actual-reference first response, now with its elementary atom and mass
premises discharged by the concrete current primary proposal. -/
theorem actual_first_response_stable (security : ℕ)
    (profile : Fin (Parameters.modulus security) → ℝ) :
    Real.sqrt (profileSquareNorm (primaryLaw security).weight
      (FirstResponse.response security profile - profile)) ≤
        Real.sqrt (profileSquareNorm (primaryLaw security).weight profile) /
          (Parameters.base security : ℝ) ^ 5 ∧
    Real.sqrt (profileSquareNorm (primaryLaw security).weight
      ((FirstResponse.responseEquiv security).symm profile)) ≤
        2 * Real.sqrt (profileSquareNorm (primaryLaw security).weight profile) := by
  exact ⟨FirstResponse.response_defect_norm_le security _ (primaryProfile_atom_lower security)
    (primaryLaw security).sum_one profile,
    FirstResponse.response_inverse_norm_le_two security _ (primaryProfile_atom_lower security)
      (primaryLaw security).sum_one profile⟩

end

end CurrentAFT.ProposalPrimary

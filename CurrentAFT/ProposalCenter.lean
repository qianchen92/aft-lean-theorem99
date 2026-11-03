import CurrentAFT.ProposalPositivity
import CurrentAFT.InwardAnchor

/-!
# The actual compensated safe-center proposal

The center law is formed from the already constructed primary law and the
actual inward smoothed anchor. Its positivity follows from current public
sizes, not from an assumed law or an assumed operator estimate.
-/

namespace CurrentAFT.ProposalPrimary

open AFT DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base DiffuseProfiles.activation
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile InwardAnchor.smoothedAnchorLaw

private theorem finite_safe_law_weight (modulus margin : ℕ) (hclear : 2 * margin < modulus)
    (color : Fin modulus) :
    (TrimmedSlice.finiteLaw modulus margin 0 (Int.natCast_nonneg _)
      (by simp only [abs_zero]; omega)).weight color =
      if (margin : ℤ) ≤ color.val ∧ (color.val : ℤ) < (modulus : ℤ) - margin then
        1 / ((modulus : ℝ) - 2 * margin) else 0 := by
  have hcard : ((TrimmedSlice.slice modulus margin 0).card : ℤ) =
        (modulus : ℤ) - 2 * margin := by
    rw [TrimmedSlice.slice_card]
    simp only [abs_zero, sub_zero]
    omega
  have hcardReal : ((TrimmedSlice.slice modulus margin 0).card : ℝ) =
        (modulus : ℝ) - 2 * margin := by
    exact_mod_cast hcard
  have hsafe : (color.val : ℤ) ∈ TrimmedSlice.slice modulus margin 0 ↔
      (margin : ℤ) ≤ color.val ∧ (color.val : ℤ) < (modulus : ℤ) - margin := by
    rw [TrimmedSlice.mem_slice]
    omega
  rw [TrimmedSlice.finiteLaw_weight]
  simp only [TrimmedSlice.law, hsafe, hcardReal, one_div]

theorem safeLaw_weight (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (safeLaw security).weight color =
      if InwardAnchor.SafeColor security color then safeHeight security else 0 := by
  have h := finite_safe_law_weight (Parameters.modulus security) (Parameters.safeMargin security)
    (by have := safe_clearance security; omega) color
  by_cases hsafe : InwardAnchor.SafeColor security color
  · have hsafe' : (Parameters.safeMargin security : ℤ) ≤ color.val ∧
        (color.val : ℤ) < (Parameters.modulus security : ℤ) - Parameters.safeMargin security := hsafe
    simpa only [safeLaw, safeHeight, if_pos hsafe, if_pos hsafe'] using h
  · have hsafe' : ¬((Parameters.safeMargin security : ℤ) ≤ color.val ∧
        (color.val : ℤ) < (Parameters.modulus security : ℤ) - Parameters.safeMargin security) := hsafe
    simpa only [safeLaw, safeHeight, if_neg hsafe, if_neg hsafe'] using h

theorem bodySize_pos (security : ℕ) : (0 : ℝ) < Parameters.bodySize security := by
  apply Nat.cast_pos.mpr
  rw [Parameters.bodySize_eq]
  exact Nat.mul_pos (Parameters.modulus_spec security).2.pos (pow_pos (Parameters.base_pos security) _)

theorem freeMass_lower (security : ℕ) : (Parameters.bodySize security : ℝ) / 2 ≤ freeMass security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hfour : 4 ≤ Parameters.base security ^ 96 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 96
    norm_num at h
    omega
  have hq : 4 * Parameters.modulus security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_left (Parameters.modulus security) hfour
    simpa only [Parameters.bodySize_eq, mul_comm _ 4] using h
  have hpow : Parameters.base security ^ 32 ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hmod := (Parameters.modulus_bounds security).1
  have hroot : 4 * Parameters.base security ^ 32 ≤ Parameters.modulus security := by omega
  have hleg : 4 * Parameters.legCount security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) hroot
    simpa only [Parameters.bodySize_eq, Parameters.legCount_eq, mul_assoc, ← pow_add] using h
  have hqr : 4 * (Parameters.modulus security : ℝ) ≤ Parameters.bodySize security := by exact_mod_cast hq
  have hlr : 4 * (Parameters.legCount security : ℝ) ≤ Parameters.bodySize security := by exact_mod_cast hleg
  unfold freeMass
  linarith

theorem freeMass_pos (security : ℕ) : 0 < freeMass security :=
  (half_pos (bodySize_pos security)).trans_le (freeMass_lower security)

def compensation (security : ℕ) : ℝ := markMass security / freeMass security

theorem compensation_nonneg (security : ℕ) : 0 ≤ compensation security :=
  div_nonneg (markMass_pos security).le (freeMass_pos security).le

theorem compensation_le_leg_body (security : ℕ) :
    compensation security ≤ (Parameters.legCount security : ℝ) / Parameters.bodySize security := by
  have hf := freeMass_pos security
  have hb := bodySize_pos security
  have hnum : markMass security ≤ (Parameters.legCount security : ℝ) / 2 := by
    unfold markMass
    nlinarith [mul_le_mul_of_nonneg_left (activation_le_half security)
      (Nat.cast_nonneg (Parameters.legCount security))]
  calc
    _ ≤ ((Parameters.legCount security : ℝ) / 2) / freeMass security :=
      div_le_div_of_nonneg_right hnum hf.le
    _ ≤ ((Parameters.legCount security : ℝ) / 2) / ((Parameters.bodySize security : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (freeMass_lower security)
    _ = _ := by ring

theorem compensation_le_one (security : ℕ) : compensation security ≤ 1 := by
  apply (compensation_le_leg_body security).trans
  apply (div_le_one (bodySize_pos security)).mpr
  exact_mod_cast (show Parameters.legCount security ≤ Parameters.bodySize security by
    have := population_room security; omega)

theorem anchor_center_budget (security : ℕ) :
    2 * Parameters.legCount security * Parameters.modulus security ≤
      Parameters.bodySize security * Parameters.anchorWidth security := by
  have hpower : 2 ≤ Parameters.base security ^ 16 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 16
    norm_num at h
    omega
  rw [Parameters.legCount_eq, Parameters.bodySize_eq, anchorWidth_eq]
  calc
    _ ≤ (Parameters.base security ^ 16) * Parameters.base security ^ 128 * Parameters.modulus security :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpower)
    _ = _ := by
      rw [show 128 = 96 + 32 by omega, show 48 = 32 + 16 by omega,
        pow_add, pow_add]
      ring

theorem centerLoss_le_half (security : ℕ) :
    compensation security * ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security) /
      Parameters.anchorWidth security ≤ 1 / 2 := by
  have hb := bodySize_pos security
  have hq := FirstResponse.modulus_pos security
  have ha : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hs : 0 ≤ (Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hbudget : 2 * (Parameters.legCount security : ℝ) * Parameters.modulus security ≤
      Parameters.bodySize security * Parameters.anchorWidth security := by exact_mod_cast anchor_center_budget security
  calc
    _ ≤ (((Parameters.legCount security : ℝ) / Parameters.bodySize security) *
        ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)) /
          Parameters.anchorWidth security :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (compensation_le_leg_body security) hs) ha.le
    _ ≤ (((Parameters.legCount security : ℝ) / Parameters.bodySize security) * Parameters.modulus security) /
        Parameters.anchorWidth security := by
      apply div_le_div_of_nonneg_right _ ha.le
      have hm0 : (0 : ℝ) ≤ Parameters.safeMargin security := Nat.cast_nonneg _
      exact mul_le_mul_of_nonneg_left (by linarith only [hm0])
        (div_nonneg (Nat.cast_nonneg (Parameters.legCount security)) hb.le)
    _ = ((Parameters.legCount security : ℝ) * Parameters.modulus security) /
        ((Parameters.bodySize security : ℝ) * Parameters.anchorWidth security) := by ring
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos hb ha)).mpr
      linarith

def anchorPrimaryLaw (security : ℕ) : FiniteDist (Fin (Parameters.modulus security)) :=
  (primaryLaw security).mix (InwardAnchor.smoothedAnchorLaw security)

theorem anchorPrimaryLaw_height (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (anchorPrimaryLaw security).weight color ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  unfold anchorPrimaryLaw
  simp only [FiniteDist.mix_weight]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (InwardAnchor.smoothedAnchorLaw_height security primary color) ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem anchorPrimaryLaw_zero_outside (security : ℕ) (color : Fin (Parameters.modulus security))
    (hunsafe : ¬InwardAnchor.SafeColor security color) : (anchorPrimaryLaw security).weight color = 0 := by
  simp only [anchorPrimaryLaw, FiniteDist.mix_weight,
    InwardAnchor.smoothedAnchorLaw_zero_outside security _ color hunsafe, mul_zero, Finset.sum_const_zero]

def centerProfile (security : ℕ) : Fin (Parameters.modulus security) → ℝ :=
  fun color => (1 + compensation security) * (safeLaw security).weight color -
    compensation security * (anchorPrimaryLaw security).weight color

theorem centerProfile_mass (security : ℕ) : ∑ color, centerProfile security color = 1 := by
  simp only [centerProfile, Finset.sum_sub_distrib, ← Finset.mul_sum, FiniteDist.sum_one, mul_one]
  ring

theorem centerProfile_zero_outside (security : ℕ) (color : Fin (Parameters.modulus security))
    (hunsafe : ¬InwardAnchor.SafeColor security color) : centerProfile security color = 0 := by
  simp only [centerProfile, safeLaw_weight, if_neg hunsafe,
    anchorPrimaryLaw_zero_outside security color hunsafe, mul_zero, sub_zero]

theorem centerProfile_bounds (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (safeLaw security).weight color / 2 ≤ centerProfile security color ∧
      centerProfile security color ≤ (1 + compensation security) * (safeLaw security).weight color := by
  have hc := compensation_nonneg security
  have hanchor := (anchorPrimaryLaw security).nonneg color
  constructor
  · by_cases hsafe : InwardAnchor.SafeColor security color
    · have hA : (0 : ℝ) < Parameters.anchorWidth security :=
        Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
      have hden : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
        have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
        push_cast at h
        linarith
      have hcost : compensation security / Parameters.anchorWidth security ≤ safeHeight security / 2 := by
        have h := (div_le_iff₀ hA).mp (centerLoss_le_half security)
        unfold safeHeight
        calc
          _ ≤ 1 / (2 * ((Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security)) := by
            apply (div_le_div_iff₀ hA (by positivity)).mpr
            nlinarith only [h]
          _ = _ := by simp only [one_div, mul_inv_rev]; ring
      have hanchorCost := mul_le_mul_of_nonneg_left (anchorPrimaryLaw_height security color) hc
      rw [mul_one_div] at hanchorCost
      rw [safeLaw_weight, if_pos hsafe]
      unfold centerProfile
      rw [safeLaw_weight, if_pos hsafe]
      nlinarith only [hcost, hanchorCost, mul_nonneg hc (safeHeight_pos security).le]
    · simp only [safeLaw_weight, if_neg hsafe, zero_div, centerProfile_zero_outside security color hsafe, le_refl]
  · unfold centerProfile
    exact sub_le_self _ (mul_nonneg hc hanchor)

def centerLaw (security : ℕ) : FiniteDist (Fin (Parameters.modulus security)) where
  weight := centerProfile security
  nonneg color := (div_nonneg ((safeLaw security).nonneg color) (by norm_num)).trans
    (centerProfile_bounds security color).1
  sum_one := centerProfile_mass security

theorem centerLaw_height (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (centerLaw security).weight color ≤ 4 / (Parameters.modulus security : ℝ) := by
  have hq := FirstResponse.modulus_pos security
  have hc0 := compensation_nonneg security
  have hc1 := compensation_le_one security
  have hsafe := safeLaw_upper security color
  have hden : (Parameters.modulus security : ℝ) / 2 ≤
      Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hheight : safeHeight security ≤ 2 / (Parameters.modulus security : ℝ) := by
    unfold safeHeight
    have h := one_div_le_one_div_of_le (by positivity : 0 < (Parameters.modulus security : ℝ) / 2) hden
    convert h using 1; ring
  have hupper := (centerProfile_bounds security color).2
  change centerProfile security color ≤ _
  have hsafeNonneg := (safeLaw security).nonneg color
  calc
    _ ≤ (1 + compensation security) * (safeLaw security).weight color := hupper
    _ ≤ 2 * (safeLaw security).weight color := by nlinarith
    _ ≤ 2 * (2 / (Parameters.modulus security : ℝ)) :=
      mul_le_mul_of_nonneg_left (hsafe.trans hheight) (by norm_num)
    _ = _ := by ring

end

end CurrentAFT.ProposalPrimary

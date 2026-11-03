import AFT.TwoPoolCanonical
import AFT.MomentActivity

/-! # Full mixed activity retains both population scales -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

local instance {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _


section Weighted

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The contribution of any actual fiber is bounded with its individual
coordinate scales. No minimum-pool substitution is made. -/
theorem fiberNorm_le_weighted_activity (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (scale : Slot → ℝ)
    (hscale : ∀ slot, 0 < scale slot) :
    MixedKernel.fiberNorm reference kernel fixed ≤
      ((∏ slot, scale slot) * (∏ slot ∈ fixed, scale slot)) *
        MixedKernel.activity (fun slot => 1 / scale slot) reference kernel := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Finset Slot)))
    (f := fun selected => (∏ slot ∈ selected, 1 / scale slot) * MixedKernel.fiberNorm reference kernel selected)
    (fun selected _ => mul_nonneg (Finset.prod_nonneg fun slot _ => (one_div_pos.mpr (hscale slot)).le)
      (MixedKernel.fiberNorm_nonneg reference kernel selected)) (Finset.mem_univ fixed)
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ∏ slot, 1 / scale slot from Finset.prod_nonneg fun slot _ => (one_div_pos.mpr (hscale slot)).le)
  have hraw : (∏ slot, 1 / scale slot) * ((∏ slot ∈ fixed, 1 / scale slot) *
      MixedKernel.fiberNorm reference kernel fixed) ≤
      MixedKernel.activity (fun slot => 1 / scale slot) reference kernel := hm
  have hh := mul_le_mul_of_nonneg_left hraw (show 0 ≤ (∏ slot, scale slot) * (∏ slot ∈ fixed, scale slot) from
    mul_nonneg (Finset.prod_nonneg fun slot _ => (hscale slot).le)
      (Finset.prod_nonneg fun slot _ => (hscale slot).le))
  have hu : (∏ slot, scale slot) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun slot _ => (hscale slot).ne')
  have hf : (∏ slot ∈ fixed, scale slot) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun slot _ => (hscale slot).ne')
  have heq : ((∏ slot, scale slot) * (∏ slot ∈ fixed, scale slot)) *
      ((∏ slot, 1 / scale slot) * ((∏ slot ∈ fixed, 1 / scale slot) *
        MixedKernel.fiberNorm reference kernel fixed)) = MixedKernel.fiberNorm reference kernel fixed := by
    simp only [one_div, Finset.prod_inv_distrib]
    field_simp
  rwa [heq] at hh

end Weighted

section TwoPools

variable {PS BS PP BP Color : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color]
  {power : ℕ}

omit [Fintype Color] [Fintype PP] [Fintype BP] in
theorem sumPattern_scope_inl (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (copy : Fin power) (label : PP) :
    Sum.inl label ∈ patternScopes (sumPattern pattern) copy ↔ label ∈ patternScopes pattern.1 copy := by
  simp only [patternScopes, Finset.mem_map, Finset.mem_univ, true_and, Sum.exists]
  simp [sumPattern]

omit [Fintype Color] [Fintype PP] [Fintype BP] in
theorem sumPattern_scope_inr (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (copy : Fin power) (label : BP) :
    Sum.inr label ∈ patternScopes (sumPattern pattern) copy ↔ label ∈ patternScopes pattern.2 copy := by
  simp only [patternScopes, Finset.mem_map, Finset.mem_univ, true_and, Sum.exists]
  simp [sumPattern]

omit [Fintype Color] [Fintype PP] [Fintype BP] in
theorem sumPattern_fixed_toLeft (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (copy : Fin power) :
    (patternFixed (sumPattern pattern) copy).toLeft = patternFixed pattern.1 copy := by
  ext slot
  simp only [Finset.mem_toLeft, patternFixed, placementFixed, Finset.mem_filter, Finset.mem_univ,
    true_and, middleScopes]
  change (_ ∧ (∃ before, before < copy ∧ _) ∧ (∃ after, copy < after ∧ _)) ↔ _
  change (Sum.inl (pattern.1 copy slot) ∈ patternScopes (sumPattern pattern) copy ∧
    (∃ before, before < copy ∧ Sum.inl (pattern.1 copy slot) ∈ patternScopes (sumPattern pattern) before) ∧
    (∃ after, copy < after ∧ Sum.inl (pattern.1 copy slot) ∈ patternScopes (sumPattern pattern) after)) ↔ _
  simp only [sumPattern_scope_inl]

omit [Fintype Color] [Fintype PP] [Fintype BP] in
theorem sumPattern_fixed_toRight (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (copy : Fin power) :
    (patternFixed (sumPattern pattern) copy).toRight = patternFixed pattern.2 copy := by
  ext slot
  simp only [Finset.mem_toRight, patternFixed, placementFixed, Finset.mem_filter, Finset.mem_univ,
    true_and, middleScopes]
  change (_ ∧ (∃ before, before < copy ∧ _) ∧ (∃ after, copy < after ∧ _)) ↔ _
  change (Sum.inr (pattern.2 copy slot) ∈ patternScopes (sumPattern pattern) copy ∧
    (∃ before, before < copy ∧ Sum.inr (pattern.2 copy slot) ∈ patternScopes (sumPattern pattern) before) ∧
    (∃ after, copy < after ∧ Sum.inr (pattern.2 copy slot) ∈ patternScopes (sumPattern pattern) after)) ↔ _
  simp only [sumPattern_scope_inr]

omit [Fintype PP] [Fintype BP] in
theorem fiberNorm_le_twoPool_activity (reference : (PS ⊕ BS) → FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ) (fixed : Finset (PS ⊕ BS))
    (primaryScale bodyScale : ℝ) (hprimary : 0 < primaryScale) (hbody : 0 < bodyScale) :
    MixedKernel.fiberNorm reference kernel fixed ≤
      primaryScale ^ (Fintype.card PS + fixed.toLeft.card) *
        bodyScale ^ (Fintype.card BS + fixed.toRight.card) *
          MixedKernel.activity (Sum.elim (fun _ : PS => 1 / primaryScale) (fun _ : BS => 1 / bodyScale)) reference kernel := by
  have h := fiberNorm_le_weighted_activity reference kernel fixed
    (Sum.elim (fun _ : PS => primaryScale) (fun _ : BS => bodyScale)) (by intro slot; cases slot <;> assumption)
  have hr : (fun slot : PS ⊕ BS => 1 / Sum.elim (fun _ : PS => primaryScale) (fun _ : BS => bodyScale) slot) =
      Sum.elim (fun _ : PS => 1 / primaryScale) (fun _ : BS => 1 / bodyScale) := by funext slot; cases slot <;> rfl
  rw [hr, Fintype.prod_sum_type, Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight] at h
  simpa only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const, Finset.card_univ, pow_add,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- The actual mixed collision contraction has one exact population power
for each pool, even for a kernel jointly depending on both pools. -/
theorem twoPool_pattern_expectation_activity_le (primary body : FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (hpattern : NoSingleton pattern.1 ∧ NoSingleton pattern.2)
    (hprimary : 0 < Fintype.card PP) (hbody : 0 < Fintype.card BP) :
    |(FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (patternProduct kernel (sumPattern pattern))| ≤
      (Fintype.card PP : ℝ) ^ (power * Fintype.card PS - (usedLabels pattern.1).card) *
        (Fintype.card BP : ℝ) ^ (power * Fintype.card BS - (usedLabels pattern.2).card) *
          MixedKernel.activity (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP))
            (fun _ : BS => 1 / Real.sqrt (Fintype.card BP)))
            (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel ^ power := by
  haveI : Nonempty Color := by
    by_contra h
    haveI : IsEmpty Color := not_nonempty_iff.mp h
    have hh := primary.sum_one
    simp at hh
  have hp : (0 : ℝ) < Fintype.card PP := by exact_mod_cast hprimary
  have hb : (0 : ℝ) < Fintype.card BP := by exact_mod_cast hbody
  have hc := pattern_expectation_sq_le_compatible
    (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))
    (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel (sumPattern pattern)
    (by intro copy slot; cases slot <;> rfl)
  rw [Finset.prod_pow] at hc
  have habs := (sq_le_sq₀ (abs_nonneg _) (Finset.prod_nonneg fun copy _ => MixedKernel.fiberNorm_nonneg _ _ _)).mp
    (by simpa only [sq_abs] using hc)
  apply habs.trans
  have h := Finset.prod_le_prod (fun copy (_ : copy ∈ (Finset.univ : Finset (Fin power))) =>
      MixedKernel.fiberNorm_nonneg (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel _)
    (fun copy (_ : copy ∈ (Finset.univ : Finset (Fin power))) => fiberNorm_le_twoPool_activity
      (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel (patternFixed (sumPattern pattern) copy)
      (Real.sqrt (Fintype.card PP)) (Real.sqrt (Fintype.card BP)) (Real.sqrt_pos.mpr hp) (Real.sqrt_pos.mpr hb))
  apply h.trans_eq
  simp only [sumPattern_fixed_toLeft, sumPattern_fixed_toRight, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpcount := patternFixed_card_sum pattern.1 hpattern.1
  have hbcount := patternFixed_card_sum pattern.2 hpattern.2
  have hpe : (∑ copy : Fin power, (Fintype.card PS + (patternFixed pattern.1 copy).card)) =
      2 * (power * Fintype.card PS - (usedLabels pattern.1).card) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hbe : (∑ copy : Fin power, (Fintype.card BS + (patternFixed pattern.2 copy).card)) =
      2 * (power * Fintype.card BS - (usedLabels pattern.2).card) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  rw [hpe, hbe, pow_mul, pow_mul, Real.sq_sqrt hp.le, Real.sq_sqrt hb.le]

end TwoPools

end

end AFT.CanonicalMoments

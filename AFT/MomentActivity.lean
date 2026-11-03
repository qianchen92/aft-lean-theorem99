import AFT.PatternContractions

/-! # The exact population powers in canonical moment contractions -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color] {power : ℕ}

omit [Fintype Pool] in
/-- Each actual mixed fiber is controlled with precisely its prescribed
integrated/fixed population powers, rather than an undifferentiated supremum. -/
theorem fiberNorm_le_scaled_activity (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (scale : ℝ) (hscale : 0 < scale) :
    MixedKernel.fiberNorm reference kernel fixed ≤
      scale ^ (Fintype.card Slot + fixed.card) * MixedKernel.activity (fun _ => 1 / scale) reference kernel := by
  have hr : 0 < 1 / scale := one_div_pos.mpr hscale
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Finset Slot)))
    (f := fun selected => (∏ _ ∈ selected, (1 / scale)) * MixedKernel.fiberNorm reference kernel selected)
    (fun selected _ => mul_nonneg (Finset.prod_nonneg fun _ _ => hr.le)
      (MixedKernel.fiberNorm_nonneg reference kernel selected)) (Finset.mem_univ fixed)
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (1 / scale) ^ Fintype.card Slot by positivity)
  have hraw : (1 / scale) ^ (Fintype.card Slot + fixed.card) * MixedKernel.fiberNorm reference kernel fixed ≤
      MixedKernel.activity (fun _ => 1 / scale) reference kernel := by
    simpa only [MixedKernel.activity, Finset.prod_const, Finset.card_univ, pow_add, mul_assoc] using hm
  have hh := mul_le_mul_of_nonneg_left hraw (show 0 ≤ scale ^ (Fintype.card Slot + fixed.card) by positivity)
  have heq : scale ^ (Fintype.card Slot + fixed.card) *
      ((1 / scale) ^ (Fintype.card Slot + fixed.card) * MixedKernel.fiberNorm reference kernel fixed) =
      MixedKernel.fiberNorm reference kernel fixed := by
    rw [← mul_assoc, ← mul_pow]
    have hcancel : scale * (1 / scale) = 1 := by field_simp
    rw [hcancel, one_pow, one_mul]
  rwa [heq] at hh

/-- Each genuine nonzero collision term has the exact mixed-activity scale;
its remaining population power is the number of lost independent labels. -/
theorem pattern_expectation_activity_le (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (pattern : Fin power → Slot ↪ Pool) (hpattern : NoSingleton pattern)
    (hpopulation : 0 < Fintype.card Pool) :
    |(FiniteDist.independent (fun _ : Pool => reference)).expectation (patternProduct kernel pattern)| ≤
      (Fintype.card Pool : ℝ) ^ (power * Fintype.card Slot - (usedLabels pattern).card) *
        MixedKernel.activity (fun _ : Slot => 1 / Real.sqrt (Fintype.card Pool))
          (fun _ => reference) kernel ^ power := by
  have hn : (0 : ℝ) < Fintype.card Pool := by exact_mod_cast hpopulation
  have hs : 0 < Real.sqrt (Fintype.card Pool : ℝ) := Real.sqrt_pos.mpr hn
  have h := Finset.prod_le_prod
    (fun copy (_ : copy ∈ (Finset.univ : Finset (Fin power))) => MixedKernel.fiberNorm_nonneg
      (fun _ : Slot => reference) kernel (patternFixed pattern copy))
    (fun copy (_ : copy ∈ (Finset.univ : Finset (Fin power))) => fiberNorm_le_scaled_activity
      (fun _ : Slot => reference) kernel (patternFixed pattern copy) (Real.sqrt (Fintype.card Pool)) hs)
  apply (pattern_expectation_abs_le reference kernel pattern).trans
  apply h.trans_eq
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcard := patternFixed_card_sum pattern hpattern
  have heq : (∑ copy : Fin power, (Fintype.card Slot + (patternFixed pattern copy).card)) =
      2 * (power * Fintype.card Slot - (usedLabels pattern).card) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  rw [heq, pow_mul, Real.sq_sqrt hn.le]

end AFT.CanonicalMoments

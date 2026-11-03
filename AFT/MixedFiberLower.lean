import AFT.FiniteRefresh

/-! # Fixed-output Hilbert fibers from a genuine reference lower bound -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- A frozen-coordinate law, multiplied by the actual probabilities of
its fixed values, is pointwise dominated by the original product law. -/
theorem frozen_weight_le (reference : Slot → FiniteDist Color)
    (fixed : Finset Slot) (values word : Slot → Color) :
    (∏ slot ∈ fixed, (reference slot).weight (values slot)) *
      (CanonicalMoments.refreshLaw reference fixedᶜ values).weight word ≤
        (FiniteDist.independent reference).weight word := by
  rw [← Fintype.prod_ite_mem fixed (fun slot => (reference slot).weight (values slot))]
  change (∏ slot, if slot ∈ fixed then (reference slot).weight (values slot) else 1) *
      (∏ slot, (if slot ∈ fixedᶜ then reference slot else CanonicalMoments.pointLaw (values slot)).weight (word slot)) ≤
    ∏ slot, (reference slot).weight (word slot)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro slot _
    exact mul_nonneg (by split_ifs; exact (reference slot).nonneg _; norm_num)
      (FiniteDist.nonneg _ _)
  · intro slot _
    by_cases hs : slot ∈ fixed
    · simp only [hs, if_true, Finset.mem_compl, not_true_eq_false, if_false, CanonicalMoments.pointLaw]
      by_cases hv : values slot = word slot
      · simp only [hv, if_true, mul_one, le_refl]
      · simp only [if_neg hv, mul_zero]
        exact (reference slot).nonneg _
    · simp only [hs, if_false, Finset.mem_compl, not_false_eq_true, if_true, one_mul, le_refl]

/-- The cost of freezing coordinates is exactly their reciprocal atom
probability. The remaining coordinates remain fully integrated. -/
theorem fiberSq_mul_weight_le (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (values : Slot → Color) :
    (∏ slot ∈ fixed, (reference slot).weight (values slot)) * fiberSq reference kernel fixed values ≤
      (FiniteDist.independent reference).l2Sq kernel := by
  have heq : fiberSq reference kernel fixed values =
      (CanonicalMoments.refreshLaw reference fixedᶜ values).expectation (fun word => kernel word ^ 2) := by
    have hh := CanonicalMoments.refresh_eq_freeze reference fixedᶜ (fun word => kernel word ^ 2) values
    simpa only [CanonicalMoments.refresh, compl_compl, fiberSq, FiniteDist.l2Sq] using hh.symm
  rw [heq]
  unfold FiniteDist.expectation FiniteDist.l2Sq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro word _
  exact (mul_le_mul_of_nonneg_right (frozen_weight_le reference fixed values word) (sq_nonneg (kernel word))).trans_eq' (by ring)

/-- A lower atom bound therefore supplies the full family of fixed-output
square estimates, with one reciprocal lower bound for each fixed slot. -/
theorem fiberSq_le_lower (reference : Slot → FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower) (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (values : Slot → Color) :
    fiberSq reference kernel fixed values ≤ (FiniteDist.independent reference).l2Sq kernel / lower ^ fixed.card := by
  apply (le_div_iff₀ (pow_pos hlower fixed.card)).mpr
  have hweight : lower ^ fixed.card ≤ ∏ slot ∈ fixed, (reference slot).weight (values slot) := by
    calc
      _ = ∏ _slot ∈ fixed, lower := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hlower.le) (fun slot _ => href slot (values slot))
  exact (mul_le_mul_of_nonneg_right hweight (fiberSq_nonneg reference kernel fixed values)).trans
    (fiberSq_mul_weight_le reference kernel fixed values) |>.trans_eq' (by ring)

/-- Every fixed fiber retains the square-root version of the same exact
atom-probability cost. -/
theorem fiberNorm_le_lower (reference : Slot → FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower) (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) :
    fiberNorm reference kernel fixed ≤
      Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) / (Real.sqrt lower) ^ fixed.card := by
  have hsqrt (n : ℕ) : Real.sqrt (lower ^ n) = (Real.sqrt lower) ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hlower.le n), ih, pow_succ]
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))).mpr
  intro values
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_sqrt (fiberSq_le_lower reference lower hlower href kernel fixed values)).trans_eq
    (by rw [Real.sqrt_div (FiniteDist.l2Sq_nonneg _ _), hsqrt])

/-- Summing the genuine mixed fibers gives one factor
`1 + rate / sqrt(lower)` for each emitted coordinate. -/
theorem activity_le_lower (reference : Slot → FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower) (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (rate : ℝ) (hrate : 0 ≤ rate) (kernel : (Slot → Color) → ℝ) :
    activity (fun _ => rate) reference kernel ≤
      rate ^ Fintype.card Slot * (1 + rate / Real.sqrt lower) ^ Fintype.card Slot *
        Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) := by
  have hexp : (∑ fixed : Finset Slot, (rate / Real.sqrt lower) ^ fixed.card) =
      (1 + rate / Real.sqrt lower) ^ Fintype.card Slot := by
    have hh := Fintype.prod_add (fun _ : Slot => rate / Real.sqrt lower) (fun _ : Slot => (1 : ℝ))
    simpa only [Finset.prod_const, Finset.card_univ, one_pow, mul_one, add_comm] using hh.symm
  unfold activity
  simp only [Finset.prod_const, Finset.card_univ]
  calc
    _ ≤ rate ^ Fintype.card Slot * ∑ fixed : Finset Slot,
        rate ^ fixed.card * (Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) / (Real.sqrt lower) ^ fixed.card) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hrate _)
      apply Finset.sum_le_sum
      intro fixed _
      exact mul_le_mul_of_nonneg_left (fiberNorm_le_lower reference lower hlower href kernel fixed) (pow_nonneg hrate _)
    _ = rate ^ Fintype.card Slot *
        ((∑ fixed : Finset Slot, (rate / Real.sqrt lower) ^ fixed.card) * Real.sqrt ((FiniteDist.independent reference).l2Sq kernel)) := by
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro fixed _
      rw [div_pow]
      ring
    _ = _ := by rw [hexp]; ring

end
end AFT.MixedKernel

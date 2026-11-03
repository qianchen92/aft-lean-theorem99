import AFT.RepresentedInputMean

/-! # Explicit polynomial supremum envelopes for literal input controls -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

theorem pool_sup_norm_le_activity (pool : Slot → ℝ) (hpool : ∀ slot, 0 < pool slot)
    (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ) :
    ‖kernel‖ ≤ (∏ slot, pool slot) * activity (fun slot => (Real.sqrt (pool slot))⁻¹) reference kernel := by
  have hr (slot) : 0 < (Real.sqrt (pool slot))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (hpool slot))
  have hs := sup_norm_le_activity (fun slot => (Real.sqrt (pool slot))⁻¹) reference kernel hr
  have hp : (∏ slot, pool slot) * (∏ slot, (Real.sqrt (pool slot))⁻¹)^2 = 1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro slot _
    rw [inv_pow, Real.sq_sqrt (hpool slot).le, mul_inv_cancel₀ (hpool slot).ne']
  calc
    _ = ((∏ slot, pool slot) * (∏ slot, (Real.sqrt (pool slot))⁻¹)^2) * ‖kernel‖ := by rw [hp, one_mul]
    _ = (∏ slot, pool slot) * ((∏ slot, (Real.sqrt (pool slot))⁻¹)^2 * ‖kernel‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (Finset.prod_nonneg fun slot _ => (hpool slot).le)

end
end AFT.MixedKernel

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance representedInputEnvelopeSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

theorem twoPoolControlKernel_norm_le (primary body : FiniteDist Color)
    (primaryPool bodyPool : ℕ) (hprimary : 0 < primaryPool) (hbody : 0 < bodyPool)
    (radius : ℝ) (hradius : 1 ≤ radius) (seeds : List (InputSeed Color))
    (order : ℕ) (horder : finiteControlCount seeds ≤ order) :
    ‖twoPoolControlKernel seeds‖ ≤ (max (primaryPool : ℝ) (bodyPool : ℝ)) ^ (2 * order) *
      (seeds.map (inputWeight primary body primaryPool bodyPool radius)).prod := by
  have hpc : Fintype.card (ControlPrimarySlot seeds) ≤ order := (controlPrimarySlot_card_le seeds).trans horder
  have hbc : Fintype.card (ControlBodySlot seeds) ≤ order := (controlBodySlot_card_le seeds).trans horder
  have hp : (0 : ℝ) < primaryPool := by exact_mod_cast hprimary
  have hb : (0 : ℝ) < bodyPool := by exact_mod_cast hbody
  have hmax : (1 : ℝ) ≤ max (primaryPool : ℝ) (bodyPool : ℝ) :=
    (by exact_mod_cast hprimary : (1 : ℝ) ≤ primaryPool).trans (le_max_left ..)
  have hh := MixedKernel.pool_sup_norm_le_activity
    (Sum.elim (fun _ : ControlPrimarySlot seeds => (primaryPool : ℝ)) (fun _ : ControlBodySlot seeds => (bodyPool : ℝ)))
    (by intro slot; cases slot <;> assumption)
    (Sum.elim (fun _ : ControlPrimarySlot seeds => primary) (fun _ : ControlBodySlot seeds => body)) (twoPoolControlKernel seeds)
  have he : (fun slot : ControlPrimarySlot seeds ⊕ ControlBodySlot seeds =>
      (Real.sqrt (Sum.elim (fun _ => (primaryPool : ℝ)) (fun _ => (bodyPool : ℝ)) slot))⁻¹) =
      Sum.elim (fun _ => 1 / Real.sqrt (primaryPool : ℝ)) (fun _ => 1 / Real.sqrt (bodyPool : ℝ)) := by
    funext slot; cases slot <;> simp
  rw [he] at hh
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_const, Finset.card_univ] at hh
  have hc : (primaryPool : ℝ) ^ Fintype.card (ControlPrimarySlot seeds) *
      (bodyPool : ℝ) ^ Fintype.card (ControlBodySlot seeds) ≤ (max (primaryPool : ℝ) (bodyPool : ℝ)) ^ (2 * order) := by
    rw [show 2 * order = order + order by omega, pow_add]
    apply mul_le_mul
      ((pow_le_pow_left₀ hp.le (le_max_left ..) _).trans (pow_le_pow_right₀ hmax hpc))
      ((pow_le_pow_left₀ hb.le (le_max_right ..) _).trans (pow_le_pow_right₀ hmax hbc)) (by positivity) (by positivity)
  have ha := twoPoolControlKernel_activity_le primary body primaryPool bodyPool radius hradius seeds
  exact hh.trans (mul_le_mul hc ha
    (MixedKernel.activity_nonneg _ _ _ (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _))) (by positivity))

theorem monomial_kernel_pointwise_envelope (primary body : FiniteDist Color)
    (primaryPool bodyPool : ℕ) (hprimary : 0 < primaryPool) (hbody : 0 < bodyPool)
    (radius : ℝ) (hradius : 1 ≤ radius) (powers : InputSeed Color →₀ ℕ)
    (order : ℕ) (horder : finiteControlCount (monomialOccurrences powers) ≤ order)
    (word : (ControlPrimarySlot (monomialOccurrences powers) ⊕ ControlBodySlot (monomialOccurrences powers)) → Color) :
    |twoPoolControlKernel (monomialOccurrences powers) word| ≤
      (max (primaryPool : ℝ) (bodyPool : ℝ)) ^ (2 * order) *
        monomialWeight (inputWeight primary body primaryPool bodyPool radius) powers := by
  have hn := twoPoolControlKernel_norm_le primary body primaryPool bodyPool hprimary hbody radius hradius
    (monomialOccurrences powers) order horder
  rw [monomialOccurrences_weight] at hn
  have hp : |twoPoolControlKernel (monomialOccurrences powers) word| ≤ ‖twoPoolControlKernel (monomialOccurrences powers)‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (twoPoolControlKernel (monomialOccurrences powers)) word
  exact hp.trans hn

end
end AFT.RepresentedPolynomial

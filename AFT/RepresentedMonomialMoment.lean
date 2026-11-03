import AFT.RepresentedTwoPoolKernel

/-! # Original seed activity controls every fixed monomial input moment -/
namespace AFT.RepresentedPolynomial
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance representedMonomialMomentSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def inputMomentEnvelope (order power : ℕ) : ℝ :=
  (power * order + 1 : ℕ) * (2 : ℝ) ^ (power * order) * (power * order + 1 : ℕ) ^ (power * order)

theorem momentConstant_le_inputMomentEnvelope (order bound power : ℕ) (horder : order ≤ bound) :
    momentConstant order power ≤ inputMomentEnvelope bound power := by
  have ho : power * order ≤ power * bound := Nat.mul_le_mul_left _ horder
  have hp : ((power * order : ℕ) : ℝ) ^ (power * order) ≤ ((power * bound + 1 : ℕ) : ℝ) ^ (power * bound) := by
    calc
      _ ≤ ((power * bound + 1 : ℕ) : ℝ) ^ (power * order) :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast ho.trans (Nat.le_succ _)) _
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (power * bound))) ho
  unfold momentConstant inputMomentEnvelope
  apply mul_le_mul _ hp (by positivity) (by positivity)
  gcongr
  norm_num

def representedInputMomentConstant (order moment : ℕ) : ℝ :=
  (max 1 (inputMomentEnvelope order (2 * moment))) ^ 2

theorem representedInputMomentConstant_nonneg (order moment : ℕ) :
    0 ≤ representedInputMomentConstant order moment := sq_nonneg _

theorem representedInputMomentConstant_ge_one (order moment : ℕ) :
    1 ≤ representedInputMomentConstant order moment := one_le_pow₀ (le_max_left ..)

variable {Color : Type*} [Fintype Color]

/-- The full arbitrary joint monomial keeps the actual two distinct pool
normalizers. The bound uses its original product of seed activities. -/
theorem monomialInputStatistic_even_moment (primary body : FiniteDist Color)
    (primaryPool bodyPool : ℕ) (hprimary : 0 < primaryPool) (hbody : 0 < bodyPool)
    (radius : ℝ) (hradius : 1 ≤ radius) (powers : InputSeed Color →₀ ℕ)
    (hc : ∀ seed ∈ powers.support, Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel)
    (order : ℕ) (horder : finiteControlCount (monomialOccurrences powers) ≤ order)
    (hprimaryLarge : 2 * order ≤ primaryPool) (hbodyLarge : 2 * order ≤ bodyPool)
    (moment : ℕ) (hmoment : 0 < moment) :
    (FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary) (fun _ : Fin bodyPool => body))).expectation
      (fun word => |monomialInputStatistic primaryPool bodyPool powers word| ^ (2 * moment)) ≤
      (representedInputMomentConstant order moment * monomialWeight (inputWeight primary body primaryPool bodyPool radius) powers) ^ (2 * moment) := by
  let seeds := monomialOccurrences powers
  have hpc : Fintype.card (ControlPrimarySlot seeds) ≤ order := (controlPrimarySlot_card_le seeds).trans horder
  have hbc : Fintype.card (ControlBodySlot seeds) ≤ order := (controlBodySlot_card_le seeds).trans horder
  have hk := twoPoolControlKernel_canonical primary body seeds
    (fun seed hs => hc seed (mem_monomialOccurrences_support powers seed hs))
  have hh := twoPoolStatistic_even_moment_le_activity (PP := Fin primaryPool) (BP := Fin bodyPool)
    primary body (twoPoolControlKernel seeds) hk moment
    (by simpa using hprimary) (by simpa using hbody)
    (by simpa using (Nat.mul_le_mul_left 2 hpc).trans hprimaryLarge)
    (by simpa using (Nat.mul_le_mul_left 2 hbc).trans hbodyLarge)
  simp only [Fintype.card_fin] at hh
  have ha := twoPoolControlKernel_activity_le primary body primaryPool bodyPool radius hradius seeds
  rw [monomialOccurrences_weight] at ha
  have hc1 := momentConstant_le_inputMomentEnvelope (Fintype.card (ControlPrimarySlot seeds)) order (2 * moment) hpc
  have hc2 := momentConstant_le_inputMomentEnvelope (Fintype.card (ControlBodySlot seeds)) order (2 * moment) hbc
  have hconst : momentConstant (Fintype.card (ControlPrimarySlot seeds)) (2 * moment) *
      momentConstant (Fintype.card (ControlBodySlot seeds)) (2 * moment) ≤
      representedInputMomentConstant order moment ^ (2 * moment) := by
    calc
      _ ≤ max 1 (inputMomentEnvelope order (2 * moment)) * max 1 (inputMomentEnvelope order (2 * moment)) :=
        mul_le_mul (hc1.trans (le_max_right ..)) (hc2.trans (le_max_right ..))
          (by unfold momentConstant; positivity) (le_trans zero_le_one (le_max_left ..))
      _ = representedInputMomentConstant order moment := by unfold representedInputMomentConstant; ring
      _ ≤ _ := le_self_pow₀ (representedInputMomentConstant_ge_one order moment) (by omega)
  have han : 0 ≤ MixedKernel.activity (Sum.elim (fun _ : ControlPrimarySlot seeds => 1 / Real.sqrt (primaryPool : ℝ))
      (fun _ : ControlBodySlot seeds => 1 / Real.sqrt (bodyPool : ℝ)))
      (Sum.elim (fun _ : ControlPrimarySlot seeds => primary) (fun _ : ControlBodySlot seeds => body)) (twoPoolControlKernel seeds) :=
    MixedKernel.activity_nonneg _ _ _ (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _))
  apply hh.trans
  rw [mul_pow]
  exact mul_le_mul hconst (pow_le_pow_left₀ han ha _) (pow_nonneg han _) (pow_nonneg (representedInputMomentConstant_nonneg order moment) _)

end
end AFT.RepresentedPolynomial

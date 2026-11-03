import AFT.TwoPoolMomentBound
import AFT.MixedFiberLower
import AFT.FiniteMomentSum

/-!
# Genuine finite-atom fixed moments with unequal public pools

The atom lower bound is applied to every actual mixed fiber. Distinct-index
collision contraction and population counting come from the generic
canonical U-statistic theorems, without any parameter-family substitution.
-/

namespace CurrentAFT.FiniteAtomMoments

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The complete mixed activity retains an individual rate for every slot
while paying the actual finite atom cost only at its fixed coordinates. -/
theorem activity_le_atom_lower (reference : Slot → FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower)
    (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (rate : Slot → ℝ) (hrate : ∀ slot, 0 ≤ rate slot) (kernel : (Slot → Color) → ℝ) :
    MixedKernel.activity rate reference kernel ≤
      (∏ slot, rate slot) * (∏ slot, (1 + rate slot / Real.sqrt lower)) *
        Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) := by
  have hexp : (∑ fixed : Finset Slot, ∏ slot ∈ fixed, rate slot / Real.sqrt lower) =
      ∏ slot, (1 + rate slot / Real.sqrt lower) := by
    have h := Fintype.prod_add (fun slot : Slot => rate slot / Real.sqrt lower) (fun _ => (1 : ℝ))
    simpa only [Finset.prod_const, one_pow, mul_one, add_comm] using h.symm
  unfold MixedKernel.activity
  calc
    _ ≤ (∏ slot, rate slot) * ∑ fixed : Finset Slot,
        (∏ slot ∈ fixed, rate slot) *
          (Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) / Real.sqrt lower ^ fixed.card) := by
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun slot _ => hrate slot)
      apply Finset.sum_le_sum
      intro fixed _
      exact mul_le_mul_of_nonneg_left
        (MixedKernel.fiberNorm_le_lower reference lower hlower href kernel fixed)
        (Finset.prod_nonneg fun slot _ => hrate slot)
    _ = (∏ slot, rate slot) *
        ((∑ fixed : Finset Slot, ∏ slot ∈ fixed, rate slot / Real.sqrt lower) *
          Real.sqrt ((FiniteDist.independent reference).l2Sq kernel)) := by
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro fixed _
      rw [Finset.prod_div_distrib, Finset.prod_const]
      ring
    _ = _ := by rw [hexp]; ring

/-- A uniform bound on the atom/rate ratios costs only a constant per
kernel slot. The two public populations retain their different rates. -/
theorem activity_le_atom_ratio (reference : Slot → FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower)
    (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (rate : Slot → ℝ) (hrate : ∀ slot, 0 ≤ rate slot)
    (ratio : ℝ) (_hratio : 0 ≤ ratio) (hcompare : ∀ slot, rate slot / Real.sqrt lower ≤ ratio)
    (kernel : (Slot → Color) → ℝ) :
    MixedKernel.activity rate reference kernel ≤
      (1 + ratio) ^ Fintype.card Slot * (∏ slot, rate slot) *
        Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) := by
  apply (activity_le_atom_lower reference lower hlower href rate hrate kernel).trans
  have hproduct : (∏ slot, (1 + rate slot / Real.sqrt lower)) ≤ (1 + ratio) ^ Fintype.card Slot := by
    calc
      _ ≤ ∏ _slot : Slot, (1 + ratio) := by
        exact Finset.prod_le_prod
          (fun slot _ => add_nonneg zero_le_one (div_nonneg (hrate slot) (Real.sqrt_nonneg _)))
          (fun slot _ => by linarith [hcompare slot])
      _ = _ := by simp
  have hrates : 0 ≤ ∏ slot, rate slot := Finset.prod_nonneg fun slot _ => hrate slot
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hproduct hrates)
    (Real.sqrt_nonneg ((FiniteDist.independent reference).l2Sq kernel))
  exact h.trans_eq (by ring)

/-- Explicit norm constant for a single fixed two-pool kernel. -/
def momentFactor (primaryOrder bodyOrder moment : ℕ) (ratio : ℝ) : ℝ :=
  (CanonicalMoments.momentConstant primaryOrder (2 * moment) *
    CanonicalMoments.momentConstant bodyOrder (2 * moment) + 1) *
      (1 + ratio) ^ (primaryOrder + bodyOrder)

theorem momentFactor_nonneg (primaryOrder bodyOrder moment : ℕ) (ratio : ℝ) (hratio : 0 ≤ ratio) :
    0 ≤ momentFactor primaryOrder bodyOrder moment ratio := by
  unfold momentFactor CanonicalMoments.momentConstant
  positivity

variable {PS BS PP BP : Type*} [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP]

local instance : DecidableEq (PS ⊕ BS) := Classical.decEq _
local instance : DecidableEq (PP ⊕ BP) := Classical.decEq _

/-- The genuine canonical statistic has a complete fixed even moment
bound from its ordinary L2 energy and actual atom/population ratios. -/
theorem twoPool_even_moment_le_energy (primary body : FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) Finset.univ kernel)
    (lower : ℝ) (hlower : 0 < lower)
    (hprimaryAtoms : ∀ color, lower ≤ primary.weight color)
    (hbodyAtoms : ∀ color, lower ≤ body.weight color)
    (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hprimaryRatio : (1 / Real.sqrt (Fintype.card PP : ℝ)) / Real.sqrt lower ≤ ratio)
    (hbodyRatio : (1 / Real.sqrt (Fintype.card BP : ℝ)) / Real.sqrt lower ≤ ratio)
    (moment : ℕ) (hmoment : 1 ≤ moment)
    (hprimary : 0 < Fintype.card PP) (hbody : 0 < Fintype.card BP)
    (hprimaryLarge : 2 * Fintype.card PS ≤ Fintype.card PP)
    (hbodyLarge : 2 * Fintype.card BS ≤ Fintype.card BP) :
    (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => |CanonicalMoments.twoPoolStatistic kernel word| ^ (2 * moment)) ≤
      (momentFactor (Fintype.card PS) (Fintype.card BS) moment ratio *
        ((1 / Real.sqrt (Fintype.card PP : ℝ)) ^ Fintype.card PS *
          (1 / Real.sqrt (Fintype.card BP : ℝ)) ^ Fintype.card BS) *
        Real.sqrt ((FiniteDist.independent (Sum.elim (fun _ : PS => primary) (fun _ : BS => body))).l2Sq kernel)) ^
          (2 * moment) := by
  have ha := activity_le_atom_ratio
    (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) lower hlower
    (by intro slot color; cases slot with
        | inl _ => exact hprimaryAtoms color
        | inr _ => exact hbodyAtoms color)
    (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP : ℝ))
      (fun _ : BS => 1 / Real.sqrt (Fintype.card BP : ℝ)))
    (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _)) ratio hratio
    (by intro slot; cases slot with
        | inl _ => exact hprimaryRatio
        | inr _ => exact hbodyRatio) kernel
  simp only [Fintype.card_sum, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_const, Finset.card_univ] at ha
  have h := CanonicalMoments.twoPoolStatistic_even_moment_le_activity
    (PP := PP) (BP := BP) primary body kernel hcanonical moment hprimary hbody hprimaryLarge hbodyLarge
  apply h.trans
  let combinatorial := CanonicalMoments.momentConstant (Fintype.card PS) (2 * moment) *
    CanonicalMoments.momentConstant (Fintype.card BS) (2 * moment)
  have hcomb : 0 ≤ combinatorial := by dsimp [combinatorial, CanonicalMoments.momentConstant]; positivity
  have hcombPower : combinatorial ≤ (combinatorial + 1) ^ (2 * moment) := by
    apply (by linarith : combinatorial ≤ combinatorial + 1).trans
    exact le_self_pow₀ (by linarith) (by omega)
  have hactivityNonneg := MixedKernel.activity_nonneg
    (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP : ℝ))
      (fun _ : BS => 1 / Real.sqrt (Fintype.card BP : ℝ)))
    (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel
    (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _))
  have hpow := pow_le_pow_left₀ hactivityNonneg ha (2 * moment)
  have hbound := mul_le_mul hcombPower hpow (pow_nonneg hactivityNonneg _) (pow_nonneg (by linarith : 0 ≤ combinatorial + 1) _)
  apply hbound.trans_eq
  simp only [momentFactor, combinatorial, mul_pow]
  ring

end

end CurrentAFT.FiniteAtomMoments

import AFT.NumericalSelectedCoefficient

/-! # Polynomial magnitudes of literal selected coefficient arrays -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

theorem referenceRestrictedComponent_abs_le (primary reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (output : selected → Color)
    (massBound atomBound : ℝ) (hm : 0 ≤ massBound) (ha : 0 ≤ atomBound)
    (hvalue : ∀ input,|mass input| ≤ massBound)
    (hatom : ∀ (slot : selected) input,|MixedKernel.referenceAtom (primary slot) (reference slot) input (output slot)| ≤ atomBound) :
    |referenceRestrictedComponent primary reference mass selected output| ≤
      (Fintype.card Color : ℝ)^Fintype.card Slot*massBound*atomBound^selected.card := by
  unfold referenceRestrictedComponent
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _input : Slot → Color,massBound*atomBound^selected.card := by
      apply Finset.sum_le_sum
      intro input _
      rw [abs_mul]
      have hp := RationalNumerics.abs_prod_le_power Finset.univ
        (fun slot : selected => MixedKernel.referenceAtom (primary slot) (reference slot) (input slot) (output slot))
        atomBound ha (fun slot _ => hatom slot (input slot))
      simpa only [Finset.card_univ,Fintype.card_coe] using
        mul_le_mul (hvalue input) hp (abs_nonneg _) hm
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,nsmul_eq_mul,Nat.cast_pow];ring

end
end AFT.LocalTensors

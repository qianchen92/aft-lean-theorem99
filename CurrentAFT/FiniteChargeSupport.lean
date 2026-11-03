import AFT.DependentFiniteChannel
import CurrentAFT.ChargedEndpoint

/-! # Exact values on the support of genuine finite kernels -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {State Source Value : Type*} [Fintype State] [Fintype Source]

def HasValue (law : FiniteDist State) (read : State → Value) (value : Value) : Prop :=
  ∀ state, law.weight state ≠ 0 → read state = value

theorem HasValue.map (law : FiniteDist Source) (record : Source → State)
    (read : State → Value) (value : Value)
    (hsupport : HasValue law (read ∘ record) value) : HasValue (law.map record) read value := by
  intro output hweight
  by_contra hvalue
  apply hweight
  rw [map_weight]
  apply Finset.sum_eq_zero
  intro source _
  by_cases hequal : record source = output
  · have hzero : law.weight source = 0 := by
      by_contra hnonzero
      exact hvalue (hequal ▸ hsupport source hnonzero)
    simp only [if_pos hequal, hzero]
  · simp only [if_neg hequal]

theorem HasValue.mix (law : FiniteDist Source) (channel : Source → FiniteDist State)
    (read : State → Value) (value : Value)
    (hsupport : ∀ source, HasValue (channel source) read value) :
    HasValue (law.mix channel) read value := by
  intro output hweight
  by_contra hvalue
  apply hweight
  rw [mix_weight]
  apply Finset.sum_eq_zero
  intro source _
  have hzero : (channel source).weight output = 0 := by
    by_contra hnonzero
    exact hvalue (hsupport source output hnonzero)
  simp only [hzero, mul_zero]

theorem HasValue.eventMass_eq (law : FiniteDist State) (read : State → Value) (value : Value)
    (hsupport : HasValue law read value) (event : Value → Prop) :
    law.eventMass (fun state => event (read state)) = if event value then 1 else 0 := by
  unfold eventMass
  dsimp only
  by_cases hvalue : event value
  · rw [if_pos hvalue]
    apply Eq.trans _ law.sum_one
    apply Finset.sum_congr rfl
    intro state _
    by_cases hzero : law.weight state = 0
    · simp only [hzero, ite_self]
    · simp only [hsupport state hzero, if_pos hvalue]
  · rw [if_neg hvalue]
    apply Finset.sum_eq_zero
    intro state _
    by_cases hzero : law.weight state = 0
    · simp only [hzero, ite_self]
    · simp only [hsupport state hzero, if_neg hvalue]

end
end AFT.FiniteDist

namespace AFT.BlockProducts
open scoped BigOperators Classical
noncomputable section
variable {Index Color Group : Type*} [Fintype Index] [Fintype Color] [AddCommMonoid Group]
  (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

theorem blockLaw_has_sum (law : ∀ index, FiniteDist (Slots index → Color))
    (value : Color → Group) (total : Index → Group)
    (hsupport : ∀ index, FiniteDist.HasValue (law index)
      (fun word => ∑ slot, value (word slot)) (total index)) :
    FiniteDist.HasValue (blockLaw Slots law)
      (fun word => ∑ coordinate, value (word coordinate)) (∑ index, total index) := by
  intro word hweight
  change (∑ coordinate, value (word coordinate)) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro index _
  apply hsupport index
  intro hzero
  apply hweight
  change (∏ index, (law index).weight (fun slot => word ⟨index, slot⟩)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ index) hzero

end
end AFT.BlockProducts

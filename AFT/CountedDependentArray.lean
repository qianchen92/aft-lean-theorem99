import AFT.CountedRationalRejection

/-! # Explicitly materialized dependent arrays

The array stores a tagged value at every integer address. The tags are
checked by construction; type transports erase during execution. No finite
function is left as a thunk that recomputes its randomized coordinate.
-/
namespace AFT.RationalRejectionProgram
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem taggedValue_eq {count : ℕ} {State : Fin count → Type*}
    {index : Fin count} {value : CountedValue (State index)}
    {tagged : (index : Fin count) × CountedValue (State index)}
    (htagged : tagged=⟨index,value⟩) (hindex : tagged.1=index) :
    cast (congrArg State hindex) tagged.2.value=value.value := by
  cases htagged
  rfl

def countedDependentArray {count : ℕ} {State : Fin count → Type*}
    (entry : (index : Fin count) → CountedValue (State index)) :
    CountedValue ((index : Fin count) → State index) :=
  let stored : Vector ((index : Fin count) × CountedValue (State index)) count :=
    Vector.ofFn (fun index => ⟨index,entry index⟩)
  ⟨fun index => cast (congrArg State (show (stored.get index).1=index from by
      have he : stored.get index=⟨index,entry index⟩ := Vector.get_ofFn _ _
      exact congrArg (fun point => point.1) he))
      (stored.get index).2.value,
    (∑ index,(stored.get index).2.work)+count⟩

theorem countedDependentArray_value {count : ℕ} {State : Fin count → Type*}
    (entry : (index : Fin count) → CountedValue (State index)) (index : Fin count) :
    (countedDependentArray entry).value index=(entry index).value := by
  unfold countedDependentArray
  dsimp only
  apply taggedValue_eq
  · exact Vector.get_ofFn _ index
  · exact congrArg (fun point : (index : Fin count) × CountedValue (State index) =>
      point.1) (Vector.get_ofFn (fun index => ⟨index,entry index⟩) index)

theorem countedDependentArray_work {count : ℕ} {State : Fin count → Type*}
    (entry : (index : Fin count) → CountedValue (State index)) (bound : ℕ)
    (hbound : ∀ index,(entry index).work≤bound) :
    (countedDependentArray entry).work≤count*(bound+1) := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun index _ => hbound index)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  have hstored : (∑ index : Fin count,
      ((Vector.ofFn (fun index => (⟨index,entry index⟩ :
        (index : Fin count) × CountedValue (State index)))).get index).2.work)=
      ∑ index,(entry index).work := by
    apply Finset.sum_congr rfl
    intro index _
    exact congrArg (fun point : (index : Fin count) × CountedValue (State index) =>
      point.2.work) (Vector.get_ofFn (fun index => ⟨index,entry index⟩) index)
  change (∑ index : Fin count,
      ((Vector.ofFn (fun index => (⟨index,entry index⟩ :
        (index : Fin count) × CountedValue (State index)))).get index).2.work)+count≤_
  rw [hstored]
  nlinarith

end AFT.RationalRejectionProgram

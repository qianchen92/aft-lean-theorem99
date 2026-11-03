import CurrentAFT.AmbientFourier

/-!
# Characters restricted to the zero-sum hyperplane

The positive-sign coordinate characters on a zero-sum endpoint agree after
adding a common frequency to every coordinate. For a nonempty coordinate
set these are exactly the equivalence classes. This statement concerns the
restriction of characters, not a claim that charge conditioning preserves
uncharged low-support cancellation.
-/

namespace CurrentAFT

open scoped BigOperators Classical

noncomputable section

variable {Index : Type*} [Fintype Index]
    {modulus : ℕ} [NeZero modulus]

/-- Frequency addition multiplies the positive-sign characters. -/
theorem coordinateCharacter_add (first second : Index → ZMod modulus) :
    coordinateCharacter (first + second) = coordinateCharacter first + coordinateCharacter second := by
  ext point
  simp only [coordinateCharacter_apply, Pi.add_apply, map_add, AddChar.add_apply,
    Finset.prod_mul_distrib]

/-- A constant frequency vector tests the sum of the endpoint coordinates. -/
theorem coordinateCharacter_constant (frequency : ZMod modulus)
    (point : Index → ZMod modulus) :
    coordinateCharacter (fun _ : Index => frequency) point =
      AddChar.zmodAddEquiv frequency (∑ index, point index) := by
  rw [coordinateCharacter_apply]
  have hsum (indices : Finset Index) :
      (∏ index ∈ indices, AddChar.zmodAddEquiv frequency (point index)) =
        AddChar.zmodAddEquiv frequency (∑ index ∈ indices, point index) := by
    induction indices using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, Finset.sum_empty, AddChar.map_zero_eq_one]
    | @insert index indices hnot ih =>
      rw [Finset.prod_insert hnot, Finset.sum_insert hnot, ih, AddChar.map_add_eq_mul]
  exact hsum Finset.univ

/-- Pointwise charge identifies frequencies modulo the all-ones direction. -/
theorem coordinateCharacter_add_constant_on_zeroSum
    (frequency point : Index → ZMod modulus) (constant : ZMod modulus)
    (hcharge : ∑ index, point index = 0) :
    coordinateCharacter (frequency + fun _ => constant) point =
      coordinateCharacter frequency point := by
  rw [coordinateCharacter_add, AddChar.add_apply, coordinateCharacter_constant,
    hcharge, AddChar.map_zero_eq_one, mul_one]

/-- A two-coordinate zero-sum test measures a difference of frequencies. -/
theorem coordinateCharacter_two_single (frequency : Index → ZMod modulus)
    (first second : Index) (value : ZMod modulus) :
    coordinateCharacter frequency (Pi.single first value - Pi.single second value) =
      AddChar.zmodAddEquiv (frequency first - frequency second) value := by
  rw [AddChar.map_sub_eq_div, coordinateCharacter_single, coordinateCharacter_single,
    map_sub, AddChar.sub_apply']

/-- For at least one coordinate, agreement on the whole zero-sum hyperplane
is exactly agreement modulo a common frequency shift. -/
theorem coordinateCharacter_equal_on_zeroSum_iff [Nonempty Index]
    (first second : Index → ZMod modulus) :
    (∀ point : Index → ZMod modulus, (∑ index, point index) = 0 →
      coordinateCharacter first point = coordinateCharacter second point) ↔
      ∃ constant : ZMod modulus, second = fun index => first index + constant := by
  constructor
  · intro hagree
    let anchor : Index := Classical.choice inferInstance
    refine ⟨second anchor - first anchor, ?_⟩
    funext index
    have hcharacter : AddChar.zmodAddEquiv (first index - first anchor) =
        AddChar.zmodAddEquiv (second index - second anchor) := by
      ext value
      have hzero : (∑ other, (Pi.single index value - Pi.single anchor value : Index → ZMod modulus) other) = 0 := by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true, sub_self]
      have hpoint := hagree (Pi.single index value - Pi.single anchor value) hzero
      rw [coordinateCharacter_two_single, coordinateCharacter_two_single] at hpoint
      exact hpoint
    have hfrequency := AddChar.zmodAddEquiv.injective hcharacter
    linear_combination -hfrequency
  · rintro ⟨constant, hsecond⟩ point hcharge
    rw [hsecond]
    exact (coordinateCharacter_add_constant_on_zeroSum first point constant hcharge).symm

end

end CurrentAFT

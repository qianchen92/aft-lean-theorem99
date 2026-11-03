import CurrentAFT.BinaryFamilyArithmetic
import CurrentAFT.RationalFamilyPowerProgram

/-! # Binary fixed-degree powers of complete joint coefficient tables -/
namespace CurrentAFT.BinaryFamilyPower
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def unit (order : ℕ) : CoefficientProgram order := fun arity _ _ =>
  let decision := matchArity order arity (zeroArity order)
  ⟨if decision.value then one else zero, decision.work+1⟩

def power (order : ℕ) (programs : List (Entry order)) (table : CoefficientProgram order) : ℕ → CoefficientProgram order
  | 0 => unit order
  | count+1 => BinaryFamilyArithmetic.multiply order programs (power order programs table count) table

theorem unit_value (order : ℕ) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (unit order arity colors centers).value.decode =
      RationalFamilyProductProgram.unit (Scalar := ℚ) order arity colors.get centers.get := by
  change (if (matchArity order arity (zeroArity order)).value = true then one else zero).decode =
    if arity = zeroArity order then (1 : ℚ) else 0
  by_cases h : (matchArity order arity (zeroArity order)).value = true
  · rw [if_pos h, if_pos ((matchArity_value order arity (zeroArity order)).mp h), one_value]
  · rw [if_neg h, if_neg (mt (matchArity_value order arity (zeroArity order)).mpr h), zero_value]

theorem unit_bounds (order : ℕ) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    HeightBound (unit order arity colors centers).value.decode 0 ∧
      (unit order arity colors centers).work ≤ 12*order+6 := by
  constructor
  · rw [unit_value]
    unfold RationalFamilyProductProgram.unit
    split_ifs
    · exact HeightBound.one
    · exact HeightBound.zero
  · exact (Nat.add_le_add_right (matchArity_work order arity (zeroArity order)) 1).trans_eq (by omega)

noncomputable section
open scoped Classical

theorem power_value (order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (table : CoefficientProgram order) (actual : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ arity colors centers, (table arity colors centers).value.decode = actual arity colors.get centers.get)
    (count : ℕ) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (power order programs table count arity colors centers).value.decode =
      RationalFamilyProductProgram.power order actual count arity colors.get centers.get := by
  induction count generalizing arity colors centers with
  | zero => exact unit_value order arity colors centers
  | succ count ih =>
    exact BinaryFamilyArithmetic.multiply_value order programs hcorrect hcomplete
      (power order programs table count) table (RationalFamilyProductProgram.power order actual count) actual
      ih hvalue arity colors centers

noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order))
    (bits : Polynomial ℕ) : ℕ → Polynomial ℕ
  | 0 => 0
  | count+1 => BinaryFamilyArithmetic.heightPolynomial order programs (heightPolynomial order programs bits count + bits)

noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order))
    (bits budget : Polynomial ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.C (12*order+6)
  | count+1 => BinaryFamilyArithmetic.workPolynomial order programs
      (heightPolynomial order programs bits count + bits) (workPolynomial order programs bits budget count + budget)

theorem polynomial_bounds (order base security : ℕ) (programs : List (Entry order))
    (table : CoefficientProgram order) (bits budget : Polynomial ℕ)
    (htable : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (table arity colors centers).value.decode (bits.eval security) ∧
        (table arity colors centers).work ≤ budget.eval security)
    (count : ℕ) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base) :
    HeightBound (power order programs table count arity colors centers).value.decode
        ((heightPolynomial order programs bits count).eval security) ∧
      (power order programs table count arity colors centers).work ≤
        (workPolynomial order programs bits budget count).eval security := by
  induction count generalizing arity colors centers with
  | zero => simpa only [power, heightPolynomial, workPolynomial, Polynomial.eval_zero, Polynomial.eval_C] using
      unit_bounds order arity colors centers
  | succ count ih =>
    have hfirst : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
        HeightBound (power order programs table count arity colors centers).value.decode
          (((heightPolynomial order programs bits count).eval security) + bits.eval security) ∧
        (power order programs table count arity colors centers).work ≤
          ((workPolynomial order programs bits budget count).eval security) + budget.eval security := by
      intro arity colors centers hc hb
      have h := ih arity colors centers hc hb
      exact ⟨h.1.mono (Nat.le_add_right _ _), h.2.trans (Nat.le_add_right _ _)⟩
    have hsecond : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
        HeightBound (table arity colors centers).value.decode
          (((heightPolynomial order programs bits count).eval security) + bits.eval security) ∧
        (table arity colors centers).work ≤
          ((workPolynomial order programs bits budget count).eval security) + budget.eval security := by
      intro arity colors centers hc hb
      have h := htable arity colors centers hc hb
      exact ⟨h.1.mono (Nat.le_add_left _ _), h.2.trans (Nat.le_add_left _ _)⟩
    simpa only [power, heightPolynomial, workPolynomial, BinaryFamilyArithmetic.heightPolynomial_eval,
      BinaryFamilyArithmetic.workPolynomial_eval, Polynomial.eval_add] using
      BinaryFamilyArithmetic.multiply_bounds order base _ _ programs (power order programs table count) table
        hfirst hsecond arity colors centers hcolors hcenters

end
end CurrentAFT.BinaryFamilyPower

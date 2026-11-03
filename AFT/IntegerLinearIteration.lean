import AFT.RationalCommonDenominator
import AFT.RationalLinearIteration

/-! # Common-denominator iteration with linear operand bit growth -/
namespace AFT.RationalNumerics
open scoped BigOperators

variable {Color : Type*} [Fintype Color]

def integerLinearIteration (denominator : ℕ) (matrix : Color → Color → ℤ)
    (rhs : Color → ℤ) : ℕ → Color → ℤ
  | 0 => 0
  | steps+1 => fun output => rhs output*(denominator : ℤ)^steps-
      ∑ input,matrix output input*integerLinearIteration denominator matrix rhs steps input

theorem integerLinearIteration_exact (denominator : ℕ) (hd : 0<denominator)
    (matrix : Color → Color → ℤ) (rhs : Color → ℤ) (steps : ℕ) (output : Color) :
    (integerLinearIteration denominator matrix rhs steps output : ℚ)/(denominator : ℚ)^steps=
      linearIteration (fun out inp => (matrix out inp : ℚ)/denominator)
        (fun out => (rhs out : ℚ)/denominator) steps output := by
  have hd0 : (denominator : ℚ)≠0 := by exact_mod_cast hd.ne'
  induction steps generalizing output with
  | zero => simp [integerLinearIteration,linearIteration]
  | succ steps ih =>
    simp only [integerLinearIteration,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
      Int.cast_sum,linearIteration,Pi.sub_apply,matrixApply]
    simp_rw [←ih]
    rw [sub_div,Finset.sum_div]
    congr 1
    · rw [pow_succ]
      field_simp
    · apply Finset.sum_congr rfl
      intro input _
      rw [pow_succ]
      field_simp

private theorem natAbs_finset_sum_le {Index : Type*} (set : Finset Index) (value : Index → ℤ) :
    (∑ index∈set,value index).natAbs≤∑ index∈set,(value index).natAbs := by
  classical
  induction set using Finset.induction_on with
  | empty => simp
  | @insert index set hnot ih =>
    rw [Finset.sum_insert hnot,Finset.sum_insert hnot]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

def iterationHeightSlope (colors coefficientBits denominatorBits : ℕ) : ℕ :=
  coefficientBits+denominatorBits+colors+1

theorem integerLinearIteration_abs_le (denominator coefficientBits denominatorBits : ℕ)
    (matrix : Color → Color → ℤ) (rhs : Color → ℤ)
    (hden : denominator≤2^denominatorBits)
    (hmatrix : ∀output input,(matrix output input).natAbs≤2^coefficientBits)
    (hrhs : ∀output,(rhs output).natAbs≤2^coefficientBits)
    (steps : ℕ) (output : Color) :
    (integerLinearIteration denominator matrix rhs steps output).natAbs≤
      2^(steps*iterationHeightSlope (Fintype.card Color) coefficientBits denominatorBits) := by
  let slope := iterationHeightSlope (Fintype.card Color) coefficientBits denominatorBits
  have hds : denominatorBits≤slope := by dsimp [slope,iterationHeightSlope];omega
  induction steps generalizing output with
  | zero => simp [integerLinearIteration]
  | succ steps ih =>
    have hdpow : denominator^steps≤2^(steps*slope) := by
      calc
        _ ≤ (2^denominatorBits)^steps := Nat.pow_le_pow_left hden _
        _ = 2^(steps*denominatorBits) := by rw [←pow_mul];congr 1;ring
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hds)
    have hfirst : (rhs output*(denominator : ℤ)^steps).natAbs≤2^coefficientBits*2^(steps*slope) := by
      simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
      exact Nat.mul_le_mul (hrhs output) hdpow
    have hsum : (∑ input,matrix output input*integerLinearIteration denominator matrix rhs steps input).natAbs≤
        Fintype.card Color*(2^coefficientBits*2^(steps*slope)) := by
      apply (natAbs_finset_sum_le Finset.univ _).trans
      calc
        _ ≤ ∑ _input : Color,2^coefficientBits*2^(steps*slope) := by
          apply Finset.sum_le_sum
          intro input _
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul (hmatrix output input) (ih input)
        _ = _ := by simp
    have hcard : Fintype.card Color+1≤2^(Fintype.card Color+1) :=
      (Nat.lt_two_pow_self (n := Fintype.card Color+1)).le
    unfold integerLinearIteration
    calc
      _ ≤ (rhs output*(denominator : ℤ)^steps).natAbs+
          (∑ input,matrix output input*integerLinearIteration denominator matrix rhs steps input).natAbs := Int.natAbs_sub_le _ _
      _ ≤ 2^coefficientBits*2^(steps*slope)+Fintype.card Color*(2^coefficientBits*2^(steps*slope)) := Nat.add_le_add hfirst hsum
      _ = (Fintype.card Color+1)*(2^coefficientBits*2^(steps*slope)) := by ring
      _ ≤ 2^(Fintype.card Color+1)*(2^coefficientBits*2^(steps*slope)) := Nat.mul_le_mul_right _ hcard
      _ = 2^(Fintype.card Color+1+coefficientBits+steps*slope) := by simp only [pow_add];ring
      _ ≤ 2^((steps+1)*slope) := by
        apply Nat.pow_le_pow_right (by decide)
        dsimp [slope,iterationHeightSlope]
        nlinarith

theorem integerLinearIteration_height (denominator coefficientBits denominatorBits : ℕ)
    (matrix : Color → Color → ℤ) (rhs : Color → ℤ)
    (hden : denominator≤2^denominatorBits)
    (hmatrix : ∀output input,(matrix output input).natAbs≤2^coefficientBits)
    (hrhs : ∀output,(rhs output).natAbs≤2^coefficientBits)
    (steps : ℕ) (output : Color) :
    HeightBound ((integerLinearIteration denominator matrix rhs steps output : ℚ)/(denominator : ℚ)^steps)
      (steps*(iterationHeightSlope (Fintype.card Color) coefficientBits denominatorBits+denominatorBits)) := by
  have hnum := HeightBound.of_int (integerLinearIteration_abs_le denominator coefficientBits denominatorBits matrix rhs hden hmatrix hrhs steps output)
  have hden := (HeightBound.of_nat hden).pow steps
  convert hnum.div hden using 1
  ring

end AFT.RationalNumerics

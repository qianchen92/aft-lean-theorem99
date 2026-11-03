import AFT.BinaryLoopControl
import AFT.ScalarOperationalEvaluation
import AFT.RootConvolutionProgram

/-! # Bounded unary window metadata

Dimension and array indices are polynomially bounded unary counters. Window
shape and signed coordinates are formed by explicit successor/case routines.
-/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

def integerDifference : ℕ → ℕ → CountedValue ℤ
  | first,0 => ⟨.ofNat first,2⟩
  | 0,second+1 => ⟨.negSucc second,2⟩
  | first+1,second+1 =>
      let previous := integerDifference first second
      ⟨previous.value,previous.work+2⟩

theorem integerDifference_value (first second : ℕ) :
    (integerDifference first second).value=(first : ℤ)-(second : ℤ) := by
  induction first generalizing second with
  | zero =>
      cases second with
      | zero => rfl
      | succ second => change Int.negSucc second=0-((second+1 : ℕ) : ℤ);omega
  | succ first ih =>
      cases second with
      | zero => simp [integerDifference]
      | succ second => simp only [integerDifference,ih,Nat.cast_add,Nat.cast_one];ring

theorem integerDifference_work (first second : ℕ) :
    (integerDifference first second).work≤ 2*(first+second)+2 := by
  induction first generalizing second with
  | zero => cases second <;> simp only [integerDifference] <;> omega
  | succ first ih =>
      cases second with
      | zero => simp only [integerDifference];omega
      | succ second => have hh := ih second;simp only [integerDifference];omega

structure WindowShape where
  cutoff : ℕ
  count : ℕ
  work : ℕ

def rootWindowShape (dimension : ℕ) : WindowShape :=
  let squared := multiplyCounter dimension dimension
  let scaled := multiplyCounter 3 squared.count
  let cutoff := scaled.count.pred
  let doubled := doubleCounter cutoff
  ⟨cutoff,doubled.count.succ,squared.work+scaled.work+doubled.work+4⟩

theorem rootWindowShape_cutoff (dimension : ℕ) :
    (rootWindowShape dimension).cutoff=3*dimension^2-1 := by
  simp only [rootWindowShape,multiplyCounter_value,Nat.pred_eq_sub_one,pow_two]

theorem rootWindowShape_count (dimension : ℕ) :
    (rootWindowShape dimension).count=2*(3*dimension^2-1)+1 := by
  simp only [rootWindowShape,multiplyCounter_value,doubleCounter_value,Nat.pred_eq_sub_one,pow_two]

theorem rootWindowShape_work (dimension : ℕ) :
    (rootWindowShape dimension).work≤ 30*(dimension+1)^2 := by
  simp only [rootWindowShape,multiplyCounter_work,multiplyCounter_value,doubleCounter_work]
  have hh : (3*(dimension*dimension)).pred≤ 3*(dimension*dimension) := Nat.pred_le _
  nlinarith

end AFT.BinaryArithmetic

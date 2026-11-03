import AFT.UnaryPolynomialCounters
import AFT.ActualLegCutoffProgram
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Actual leg cutoff with counted integer metadata computation

The fixed powers and bounded search use unary counters. Their magnitudes have
explicit polynomial bounds, so this avoids any unit-cost large-integer test.
-/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram V7Calibration Polynomial
open scoped BigOperators

def legCutoffTest (threshold index : ℕ) : CountedValue Bool :=
  let powered := powerCounter index 8
  let comparison := lessCounter powered.count threshold
  ⟨comparison.value,powered.work+comparison.work+2⟩

theorem legCutoffTest_value (threshold index : ℕ) :
    (legCutoffTest threshold index).value=true ↔ index^8<threshold := by
  simp only [legCutoffTest,lessCounter_value,powerCounter_value]

theorem legCutoffTest_work (threshold index limit : ℕ) (hi : index≤limit) :
    (legCutoffTest threshold index).work≤powerCounterWork limit 8+3*(limit^8+threshold)+4 := by
  have hp := (powerCounter_work index 8).trans (powerCounterWork_mono hi 8)
  have hc := lessCounter_work (powerCounter index 8).count threshold
  rw [powerCounter_value] at hc
  have hm := Nat.pow_le_pow_left hi 8
  simp only [legCutoffTest,powerCounter_value]
  omega

def binaryLegCutoff (constant n : ℕ) : UnaryCounterResult :=
  let square := multiplyCounter n n
  let range := multiplyCounter constant square.count
  let factor := powerCounter constant 8
  let powered := powerCounter n 9
  let threshold := multiplyCounter factor.count powered.count
  let counted := countFin range.count.succ (fun index => legCutoffTest threshold.count index.val)
  ⟨counted.count,square.work+range.work+factor.work+powered.work+threshold.work+counted.work+7⟩

theorem binaryLegCutoff_value (constant n : ℕ) :
    (binaryLegCutoff constant n).count=actualLegCutoffProgram constant n := by
  simp only [binaryLegCutoff,countFin_value]
  simp_rw [show ∀ threshold index,(legCutoffTest threshold index).value=true ↔ index^8<threshold from legCutoffTest_value]
  simp only [multiplyCounter_value,powerCounter_value]
  unfold actualLegCutoffProgram
  rw [Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range
    (fun index => if index^8<constant^8*n^9 then (1 : ℕ) else 0)
    (multiplyCounter constant (multiplyCounter n n).count).count.succ]
  simp only [multiplyCounter_value,pow_two]

def binaryLegCutoffWork (constant n : ℕ) : ℕ :=
  n*(2*n+3)+constant*(2*n^2+3)+powerCounterWork constant 8+powerCounterWork n 9+
    constant^8*(2*n^9+3)+
    (constant*n^2+1)*(powerCounterWork (constant*n^2+1) 8+3*((constant*n^2+1)^8+constant^8*n^9)+7)+12

theorem binaryLegCutoff_work (constant n : ℕ) :
    (binaryLegCutoff constant n).work≤binaryLegCutoffWork constant n := by
  have wf := powerCounter_work constant 8
  have wp := powerCounter_work n 9
  have hentry (index : Fin (multiplyCounter constant (multiplyCounter n n).count).count.succ) :
      (legCutoffTest (multiplyCounter (powerCounter constant 8).count (powerCounter n 9).count).count index).work≤
        powerCounterWork (constant*n^2+1) 8+3*((constant*n^2+1)^8+constant^8*n^9)+4 := by
    have hi := index.isLt
    simp only [multiplyCounter_value,powerCounter_value,pow_two] at hi ⊢
    exact legCutoffTest_work _ _ _ (by omega)
  have wc := countFin_work (multiplyCounter constant (multiplyCounter n n).count).count.succ
    (powerCounterWork (constant*n^2+1) 8+3*((constant*n^2+1)^8+constant^8*n^9)+4)
    (fun index => legCutoffTest (multiplyCounter (powerCounter constant 8).count (powerCounter n 9).count).count index.val) hentry
  simp only [binaryLegCutoff,multiplyCounter_work,multiplyCounter_value,powerCounter_value,binaryLegCutoffWork,pow_two] at wc ⊢
  nlinarith

noncomputable def powerCounterPolynomial (base : Polynomial ℕ) (exponent : ℕ) : Polynomial ℕ :=
  C (exponent+1)*(6*(base+1)^(exponent+2)+4)
noncomputable def binaryLegCutoffPolynomial (constant : ℕ) : Polynomial ℕ :=
  X*(2*X+3)+C constant*(2*X^2+3)+powerCounterPolynomial (C constant) 8+powerCounterPolynomial X 9+
    C constant^8*(2*X^9+3)+
    (C constant*X^2+1)*(powerCounterPolynomial (C constant*X^2+1) 8+
      3*((C constant*X^2+1)^8+C constant^8*X^9)+7)+12

@[simp] theorem powerCounterPolynomial_eval (base : Polynomial ℕ) (exponent n : ℕ) :
    (powerCounterPolynomial base exponent).eval n=powerCounterWork (base.eval n) exponent := by
  simp only [powerCounterPolynomial,powerCounterWork,eval_mul,eval_add,eval_pow,eval_C,eval_ofNat,eval_one]
@[simp] theorem binaryLegCutoffPolynomial_eval (constant n : ℕ) :
    (binaryLegCutoffPolynomial constant).eval n=binaryLegCutoffWork constant n := by
  simp only [binaryLegCutoffPolynomial,binaryLegCutoffWork,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_ofNat,
    eval_one,powerCounterPolynomial_eval]

end AFT.BinaryArithmetic

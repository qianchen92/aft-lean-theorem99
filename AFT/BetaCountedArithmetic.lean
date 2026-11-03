import AFT.BetaIntegerSampler

/-! # Checked arithmetic-operation counts for the concrete beta CDF evaluator

The counter records integer additions, multiplications and natural divisions.
It is not a Turing-machine cost model; binary operand bounds are proved
separately in `BetaIntegerArithmetic` and `ActualBetaNumericalBounds`.
-/
namespace AFT.BetaReference

structure CountedInteger where
  value : ℤ
  work : ℕ

namespace CountedInteger

def literal (value : ℤ) : CountedInteger := ⟨value,0⟩
def add (first second : CountedInteger) : CountedInteger :=
  ⟨first.value+second.value,first.work+second.work+1⟩
def mul (first second : CountedInteger) : CountedInteger :=
  ⟨first.value*second.value,first.work+second.work+1⟩
def natDiv (first second : CountedInteger) : CountedInteger :=
  ⟨first.value.toNat/second.value.toNat,first.work+second.work+1⟩

def power (value : ℤ) : ℕ → CountedInteger
  | 0 => literal 1
  | exponent+1 => (power value exponent).mul (literal value)

def factorial : ℕ → CountedInteger
  | 0 => literal 1
  | n+1 => (literal (n+1)).mul (factorial n)

@[simp] theorem power_value (value : ℤ) (exponent : ℕ) : (power value exponent).value=value^exponent := by
  induction exponent with
  | zero => simp [power,literal]
  | succ exponent ih => simp only [power,mul,literal,ih,pow_succ]

@[simp] theorem power_work (value : ℤ) (exponent : ℕ) : (power value exponent).work=exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp only [power,mul,literal,ih,Nat.add_zero]

@[simp] theorem factorial_value (n : ℕ) : (factorial n).value=n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorial,mul,literal,ih,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]

@[simp] theorem factorial_work (n : ℕ) : (factorial n).work=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorial,mul,literal,ih,Nat.zero_add]

/-- Factorials and an exact integer division implement the actual binomial
coefficient; its standard combinatorial recursion is not used. -/
def choose (n j : ℕ) : CountedInteger :=
  (factorial n).natDiv ((factorial j).mul (factorial (n-j)))

theorem choose_value (n j : ℕ) (hj : j ≤ n) : (choose n j).value=n.choose j := by
  simp only [choose,natDiv,mul,factorial_value,← Nat.cast_mul,Int.toNat_natCast]
  exact_mod_cast (Nat.choose_eq_factorial_div_factorial hj).symm

theorem choose_work (n j : ℕ) (hj : j ≤ n) : (choose n j).work=2*n+2 := by
  simp only [choose,natDiv,mul,factorial_work]
  omega

/-- This concrete evaluator computes one summand of the exact integer CDF. -/
def cdfTerm (K n M a j : ℕ) : CountedInteger :=
  ((((power (-1) j).mul ((factorial (K+n+1)).natDiv (literal ((K+j+1 : ℕ) : ℤ)))).mul (choose n j)).mul
    (power a (K+j+1))).mul (power M (n-j))

theorem cdfTerm_value (K n M a j : ℕ) (hj : j ≤ n) :
    (cdfTerm K n M a j).value=integerCDFTerm K n M a j := by
  simp only [cdfTerm,mul,natDiv,literal,power_value,factorial_value,choose_value n j hj,
    Int.toNat_natCast,integerCDFTerm,Int.natCast_ediv]

theorem cdfTerm_work_le (K n M a j : ℕ) (hj : j ≤ n) :
    (cdfTerm K n M a j).work ≤ 12*(K+n+1) := by
  simp only [cdfTerm,mul,natDiv,literal,power_work,factorial_work,choose_work n j hj]
  omega

/-- The running sum is evaluated recursively, in exactly the same order
as the literal polynomial numerator. -/
def cdfPrefix (K n M a : ℕ) : ℕ → CountedInteger
  | 0 => literal 0
  | length+1 => (cdfPrefix K n M a length).add (cdfTerm K n M a length)

theorem cdfPrefix_value (K n M a length : ℕ) (hl : length ≤ n+1) :
    (cdfPrefix K n M a length).value=integerCDFPrefix K n M a length := by
  induction length with
  | zero => simp [cdfPrefix,literal,integerCDFPrefix]
  | succ length ih =>
    simp only [cdfPrefix,add,ih (by omega),cdfTerm_value K n M a length (by omega)]
    exact (Finset.sum_range_succ _ _).symm

theorem cdfPrefix_work_le (K n M a length : ℕ) (hl : length ≤ n+1) :
    (cdfPrefix K n M a length).work ≤ length*(12*(K+n+1)+1) := by
  induction length with
  | zero => simp [cdfPrefix,literal]
  | succ length ih =>
    have hp := ih (by omega)
    have ht := cdfTerm_work_le K n M a length (by omega)
    simp only [cdfPrefix,add]
    calc
      _ ≤ length*(12*(K+n+1)+1)+12*(K+n+1)+1 := Nat.add_le_add_right (Nat.add_le_add hp ht) 1
      _ = _ := by ring

def cdfDenominator (K n M : ℕ) : CountedInteger :=
  ((factorial K).mul (factorial n)).mul (power M (K+n+1))

@[simp] theorem cdfDenominator_value (K n M : ℕ) :
    (cdfDenominator K n M).value=integerCDFDenominator K n M := by
  simp only [cdfDenominator,mul,factorial_value,power_value,integerCDFDenominator,Nat.cast_mul,Nat.cast_pow]

theorem cdfDenominator_work_le (K n M : ℕ) :
    (cdfDenominator K n M).work ≤ 3*(K+n+1) := by
  simp only [cdfDenominator,mul,factorial_work,power_work]
  omega

/-- Query evaluator after the grid base `M` has been computed once. -/
def cdfCut (K n M bits a : ℕ) : CountedInteger :=
  ((power 2 bits).mul (cdfPrefix K n M a (n+1))).natDiv (cdfDenominator K n M)

theorem cdfCut_value (K n depth bits a : ℕ) (ha : a ≤ 2^depth) :
    (cdfCut K n (2^depth) bits a).value=integerCut K n depth bits a := by
  have hr := integerCDFNumerator_range K n (2^depth) a (by positivity) ha
  simp only [cdfCut,natDiv,mul,power_value,cdfPrefix_value K n (2^depth) a (n+1) le_rfl,
    integerCDFPrefix_full,cdfDenominator_value,Int.toNat_natCast,integerCut]
  rw [Int.toNat_mul (by positivity) hr.1]
  rw [Int.toNat_pow_of_nonneg (by norm_num : 0 ≤ (2 : ℤ))]
  rfl

theorem cdfCut_work_le (K n M bits a : ℕ) :
    (cdfCut K n M bits a).work ≤ 18*(K+n+1)^2+bits := by
  have hp := cdfPrefix_work_le K n M a (n+1) le_rfl
  have hd := cdfDenominator_work_le K n M
  have hlen : n+1 ≤ K+n+1 := by omega
  have hprod := Nat.mul_le_mul_right (12*(K+n+1)+1) hlen
  simp only [cdfCut,natDiv,mul,power_work]
  nlinarith

end CountedInteger
end AFT.BetaReference

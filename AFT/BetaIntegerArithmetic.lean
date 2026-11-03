import AFT.BetaIntegerCDF

/-! # Binary-size bounds for the concrete integer beta evaluator -/
namespace AFT.BetaReference
open scoped BigOperators

/-- A literal summand of the executable common-denominator numerator. -/
def integerCDFTerm (K n M a j : ℕ) : ℤ :=
  (-1 : ℤ)^j*((K+n+1).factorial/(K+j+1) : ℕ)*(n.choose j : ℕ)*
    (a : ℤ)^(K+j+1)*(M : ℤ)^(n-j)

def integerCDFPrefix (K n M a length : ℕ) : ℤ :=
  ∑ j ∈ Finset.range length,integerCDFTerm K n M a j

theorem integerCDFPrefix_full (K n M a : ℕ) :
    integerCDFPrefix K n M a (n+1)=integerCDFNumerator K n M a := rfl

theorem integerCDFTerm_natAbs_le (K n M a j : ℕ) (ha : a ≤ M) (hj : j ≤ n) :
    (integerCDFTerm K n M a j).natAbs ≤ (K+n+1).factorial*2^n*M^(K+n+1) := by
  simp only [integerCDFTerm,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,Int.natAbs_natCast]
  have hcoeff := Nat.mul_le_mul (Nat.div_le_self (K+n+1).factorial (K+j+1)) (Nat.choose_le_two_pow n j)
  have hpower : a^(K+j+1)*M^(n-j) ≤ M^(K+n+1) := by
    calc
      _ ≤ M^(K+j+1)*M^(n-j) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ha _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  calc
    _ = ((K+n+1).factorial/(K+j+1)*(n.choose j))*(a^(K+j+1)*M^(n-j)) := by ring
    _ ≤ _ := Nat.mul_le_mul hcoeff hpower

/-- Every partial sum, including alternating intermediate sums, has a
polynomial binary-size envelope. -/
theorem integerCDFPrefix_natAbs_le (K n M a length : ℕ) (ha : a ≤ M) (hl : length ≤ n+1) :
    (integerCDFPrefix K n M a length).natAbs ≤
      length*((K+n+1).factorial*2^n*M^(K+n+1)) := by
  induction length with
  | zero => simp [integerCDFPrefix]
  | succ length ih =>
    rw [integerCDFPrefix,Finset.sum_range_succ]
    have hh := Int.natAbs_add_le (integerCDFPrefix K n M a length) (integerCDFTerm K n M a length)
    have hterm := integerCDFTerm_natAbs_le K n M a length ha (by omega)
    exact hh.trans ((Nat.add_le_add (ih (by omega)) hterm).trans_eq (by ring))

private theorem factorial_binary_bound (N : ℕ) : N.factorial ≤ 2^(N^2) := by
  apply (Nat.factorial_le_pow N).trans
  have hh := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n:=N))) N
  simpa only [pow_mul,pow_two] using hh

theorem integerCDFPrefix_binary_bound (K n depth a length : ℕ)
    (ha : a ≤ 2^depth) (hl : length ≤ n+1) :
    (integerCDFPrefix K n (2^depth) a length).natAbs ≤
      2^((K+n+1)^2*3+depth*(K+n+1)) := by
  let N := K+n+1
  have hlen : length ≤ 2^N := (show length ≤ N by omega).trans (Nat.lt_two_pow_self (n:=N)).le
  have hn : 2^n ≤ 2^N := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbound := integerCDFPrefix_natAbs_le K n (2^depth) a length ha hl
  calc
    _ ≤ length*(N.factorial*2^n*(2^depth)^N) := hbound
    _ ≤ 2^N*(2^(N^2)*2^N*(2^depth)^N) := Nat.mul_le_mul hlen
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul (factorial_binary_bound N) hn))
    _ = 2^(N^2+2*N+depth*N) := by
      rw [← pow_mul,← pow_add,← pow_add,← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by dsimp [N]; nlinarith)

/-- Binary length of every running numerator sum in an actual CDF query. -/
theorem integerCDFPrefix_bitSize (K n depth a length : ℕ)
    (ha : a ≤ 2^depth) (hl : length ≤ n+1) :
    (integerCDFPrefix K n (2^depth) a length).natAbs.size ≤
      (K+n+1)^2*3+depth*(K+n+1)+1 := by
  exact (Nat.size_le_size (integerCDFPrefix_binary_bound K n depth a length ha hl)).trans_eq Nat.size_pow

theorem integerCDFDenominator_bitSize (K n depth : ℕ) :
    (integerCDFDenominator K n (2^depth)).size ≤ (K+n+1)^2*2+depth*(K+n+1)+1 :=
  (Nat.size_le_size (integerCDFDenominator_binary_bound K n depth)).trans_eq Nat.size_pow

theorem integerCDFNumerator_bitSize (K n depth a : ℕ) (ha : a ≤ 2^depth) :
    (integerCDFNumerator K n (2^depth) a).natAbs.size ≤ (K+n+1)^2*2+depth*(K+n+1)+1 := by
  have hr := integerCDFNumerator_range K n (2^depth) a (by positivity) ha
  have hb : (integerCDFNumerator K n (2^depth) a).natAbs ≤ integerCDFDenominator K n (2^depth) := by
    exact_mod_cast (by simpa only [Int.natCast_natAbs,abs_of_nonneg hr.1] using hr.2 :
      ((integerCDFNumerator K n (2^depth) a).natAbs : ℤ) ≤ (integerCDFDenominator K n (2^depth) : ℤ))
  exact (Nat.size_le_size hb).trans (integerCDFDenominator_bitSize K n depth)

/-- The ticket-scaled numerator used by the actual cumulative division. -/
theorem integerTicketNumerator_bitSize (K n depth bits a : ℕ) (ha : a ≤ 2^depth) :
    (2^bits*(integerCDFNumerator K n (2^depth) a).toNat).size ≤
      bits+(K+n+1)^2*2+depth*(K+n+1)+1 := by
  have hr := integerCDFNumerator_range K n (2^depth) a (by positivity) ha
  have hnum : (integerCDFNumerator K n (2^depth) a).toNat ≤ integerCDFDenominator K n (2^depth) := by
    exact_mod_cast (by simpa only [Int.toNat_of_nonneg hr.1] using hr.2 :
      (((integerCDFNumerator K n (2^depth) a).toNat : ℕ) : ℤ) ≤ integerCDFDenominator K n (2^depth))
  have hh := Nat.mul_le_mul_left (2^bits) (hnum.trans (integerCDFDenominator_binary_bound K n depth))
  rw [← pow_add] at hh
  have hs := (Nat.size_le_size hh).trans_eq Nat.size_pow
  convert hs using 1
  omega

/-- Integer division replaces the rational floor in the actual CDF query. -/
def integerCut (K n depth bits a : ℕ) : ℕ :=
  (2^bits*(integerCDFNumerator K n (2^depth) a).toNat)/integerCDFDenominator K n (2^depth)

theorem integerCut_eq_finiteCut (K n depth bits a : ℕ) (ha : a ≤ 2^depth) :
    integerCut K n depth bits a=finiteCut K n depth bits a := by
  have hr := integerCDFNumerator_range K n (2^depth) a (by positivity) ha
  have he : (((integerCDFNumerator K n (2^depth) a).toNat : ℕ) : ℚ)=
      (integerCDFNumerator K n (2^depth) a : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hr.1
  rw [finiteCut_integer_formula,← he,← Nat.cast_mul,Nat.floor_div_natCast,Nat.floor_natCast]
  rfl

end AFT.BetaReference

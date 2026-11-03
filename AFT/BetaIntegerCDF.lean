import AFT.BetaFiniteSampler

/-! # An integer common-denominator evaluator for the exact beta CDF -/
namespace AFT.BetaReference
open scoped BigOperators

/-- A common integer denominator for the exact CDF at a grid point. -/
def integerCDFDenominator (K n M : ℕ) : ℕ := K.factorial*n.factorial*M^(K+n+1)

/-- Finite integer arithmetic version of the same polynomial integral.
The division in each coefficient is exact because its divisor is at most
the population whose factorial appears in the numerator. -/
def integerCDFNumerator (K n M a : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n+1),(-1 : ℤ)^j*((K+n+1).factorial/(K+j+1) : ℕ)*
    (n.choose j : ℕ)*(a : ℤ)^(K+j+1)*(M : ℤ)^(n-j)

def integerCDF (K n M a : ℕ) : ℚ :=
  (integerCDFNumerator K n M a : ℚ)/(integerCDFDenominator K n M : ℕ)

theorem integerCDF_eq_rationalCDF (K n M a : ℕ) (hM : 0 < M) :
    integerCDF K n M a=rationalCDF K n ((a : ℚ)/M) := by
  have hMp : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hK : (K.factorial : ℚ) ≠ 0 := by positivity
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  unfold integerCDF integerCDFNumerator integerCDFDenominator rationalCDF
  simp only [Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast,Nat.cast_mul,Nat.cast_pow]
  rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  have hd : K+j+1 ∣ (K+n+1).factorial := Nat.dvd_factorial (by omega) (by omega)
  rw [Nat.cast_div_charZero hd]
  have he : (K+j+1 : ℚ) ≠ 0 := by positivity
  have hpow : (M : ℚ)^(K+j+1)*(M : ℚ)^(n-j)=(M : ℚ)^(K+n+1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [div_pow]
  field_simp
  rw [← hpow]
  ring

theorem integerCDFDenominator_positive (K n M : ℕ) (hM : 0 < M) : 0 < integerCDFDenominator K n M := by
  unfold integerCDFDenominator
  positivity

/-- For every queried grid point the common-denominator numerator is an
integer in the actual probability range. -/
theorem integerCDFNumerator_range (K n M a : ℕ) (hM : 0 < M) (ha : a ≤ M) :
    0 ≤ integerCDFNumerator K n M a ∧ integerCDFNumerator K n M a ≤ integerCDFDenominator K n M := by
  have hden : (0 : ℚ) < integerCDFDenominator K n M := by exact_mod_cast integerCDFDenominator_positive K n M hM
  have hzero := rationalCDF_mono K n (x:=0) (y:=(a : ℚ)/M) le_rfl (by positivity)
    ((div_le_one (by exact_mod_cast hM : (0 : ℚ) < M)).mpr (by exact_mod_cast ha))
  have hone := rationalCDF_mono K n (x:=(a : ℚ)/M) (y:=1) (by positivity)
    ((div_le_one (by exact_mod_cast hM : (0 : ℚ) < M)).mpr (by exact_mod_cast ha)) le_rfl
  rw [rationalCDF_zero,← integerCDF_eq_rationalCDF K n M a hM] at hzero
  rw [rationalCDF_one,← integerCDF_eq_rationalCDF K n M a hM] at hone
  change 0 ≤ (integerCDFNumerator K n M a : ℚ)/(integerCDFDenominator K n M : ℕ) at hzero
  change (integerCDFNumerator K n M a : ℚ)/(integerCDFDenominator K n M : ℕ) ≤ 1 at hone
  constructor
  · exact_mod_cast (div_nonneg_iff.mp hzero).elim And.left (fun h => False.elim ((not_le_of_gt hden) h.2))
  · exact_mod_cast (div_le_one hden).mp hone

/-- No integer in the exact CDF denominator needs exponentially many bits:
this explicit binary exponent is polynomial in the population and depth. -/
theorem integerCDFDenominator_binary_bound (K n depth : ℕ) :
    integerCDFDenominator K n (2^depth) ≤ 2^((K+n+1)^2*2+depth*(K+n+1)) := by
  let N := K+n+1
  have hK : K.factorial ≤ 2^(N^2) := by
    apply (Nat.factorial_le (show K ≤ N by omega)).trans
    apply (Nat.factorial_le_pow N).trans
    have hh := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n:=N))) N
    simpa only [pow_mul,pow_two] using hh
  have hn : n.factorial ≤ 2^(N^2) := by
    apply (Nat.factorial_le (show n ≤ N by omega)).trans
    apply (Nat.factorial_le_pow N).trans
    have hh := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n:=N))) N
    simpa only [pow_mul,pow_two] using hh
  calc
    integerCDFDenominator K n (2^depth) ≤ (2^(N^2)*2^(N^2))*(2^depth)^N :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hK hn)
    _ = _ := by rw [← pow_add,← pow_mul,← pow_add]; congr 1; dsimp [N]; ring

/-- The cumulative ticket evaluator can use only the checked integer
numerator and denominator, and returns exactly the existing sampler cutoff. -/
theorem finiteCut_integer_formula (K n depth bits a : ℕ) :
    finiteCut K n depth bits a=
      ⌊((2^bits : ℕ) : ℚ)*(integerCDFNumerator K n (2^depth) a : ℚ)/
        (integerCDFDenominator K n (2^depth) : ℕ)⌋₊ := by
  unfold finiteCut gridCDF
  rw [← integerCDF_eq_rationalCDF K n (2^depth) a (by positivity)]
  unfold integerCDF
  congr 1
  ring

end AFT.BetaReference

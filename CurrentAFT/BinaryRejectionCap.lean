import CurrentAFT.PublicParameterProgram
import AFT.UnaryPolynomialCounters
import AFT.Negligible

/-! Executed polynomial rejection cap and its exact exponential timeout. -/
namespace CurrentAFT.BinaryRejectionCap
open AFT BinaryArithmetic
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus multiplyCounter

def current (security : ℕ) : UnaryCounterResult :=
  let prime := PublicParameterProgram.modulus security
  let scaled := multiplyCounter 8 prime.count
  let result := multiplyCounter scaled.count security
  ⟨result.count, prime.work+scaled.work+result.work+3⟩

theorem current_value (security : ℕ) : (current security).count = 8*Parameters.modulus security*security := by
  simp only [current, multiplyCounter_value, PublicParameterProgram.modulus_value]

noncomputable def countPolynomial : Polynomial ℕ := 8*(131072*(Polynomial.X+2)^64)*Polynomial.X
noncomputable def workPolynomial : Polynomial ℕ := PublicParameterProgram.workPolynomial+
  8*(2*(131072*(Polynomial.X+2)^64)+3)+1+(8*(131072*(Polynomial.X+2)^64))*(2*Polynomial.X+3)+1+3

theorem count_bound (security : ℕ) : (current security).count ≤ countPolynomial.eval security := by
  rw [current_value]
  have hq : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  simp only [countPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  exact Nat.mul_le_mul_right security (Nat.mul_le_mul_left 8 hq)

theorem current_work (security : ℕ) : (current security).work ≤ workPolynomial.eval security := by
  have hq : (PublicParameterProgram.modulus security).count ≤ 131072*(security+2)^64 := by
    rw [PublicParameterProgram.modulus_value]
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hw := PublicParameterProgram.modulus_polynomial_work security
  have hs := multiplyCounter_work 8 (PublicParameterProgram.modulus security).count
  have hr := multiplyCounter_work (multiplyCounter 8 (PublicParameterProgram.modulus security).count).count security
  have hr' : (multiplyCounter (multiplyCounter 8 (PublicParameterProgram.modulus security).count).count security).work ≤
      (8*(PublicParameterProgram.modulus security).count)*(2*security+3)+1 := by
    simpa only [multiplyCounter_value] using hr.le
  have hscaled := Nat.add_le_add_right (Nat.mul_le_mul_left 8 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hq) 3)) 1
  have hresult := Nat.add_le_add_right (Nat.mul_le_mul_right (2*security+3) (Nat.mul_le_mul_left 8 hq)) 1
  change (PublicParameterProgram.modulus security).work+(multiplyCounter 8 (PublicParameterProgram.modulus security).count).work+
    (multiplyCounter (multiplyCounter 8 (PublicParameterProgram.modulus security).count).count security).work+3 ≤ _
  simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

theorem timeout_value (security : ℕ) :
    Real.exp (-((current security).count : ℝ)/(8*(Parameters.modulus security : ℝ))) = Real.exp (-(security : ℝ)) := by
  rw [current_value]
  congr 1
  push_cast
  have hq : (Parameters.modulus security : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr (Parameters.modulus_spec security).2.ne_zero)
  field_simp

theorem timeout_negligible : Negligible (fun security =>
    Real.exp (-((current security).count : ℝ)/(8*(Parameters.modulus security : ℝ)))) := by
  have h := negligible_polynomial_stretched_exponential 1 0 1 1 (by norm_num) (by norm_num) (by norm_num)
  simpa only [timeout_value, pow_zero, mul_one, one_mul, Real.rpow_one, neg_mul, neg_neg] using h

end CurrentAFT.BinaryRejectionCap

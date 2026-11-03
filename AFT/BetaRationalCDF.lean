import AFT.BetaReference

/-! # An executable exact rational CDF for the integer beta distribution

Only rational arithmetic and finite sums occur in `rationalCDF`.  The
identity with the genuine beta integral is proved below; no real-number
comparison or integration oracle is part of its evaluation.
-/
namespace AFT.BetaReference
open MeasureTheory
open scoped BigOperators

/-- Exact rational evaluation of the beta CDF at a rational point. -/
def rationalCDF (K n : ℕ) (x : ℚ) : ℚ :=
  ((K+n+1).factorial : ℚ)/(K.factorial*n.factorial)*
    ∑ j∈Finset.range (n+1),(n.choose j : ℚ)*(-1)^j*x^(K+j+1)/(K+j+1 : ℕ)

/-- The finite polynomial expansion being integrated by the evaluator. -/
theorem density_sum (K n : ℕ) (x : ℝ) :
    density K n x=∑ j∈Finset.range (n+1),
      (((K+n+1).factorial : ℝ)/(K.factorial*n.factorial)*(n.choose j : ℝ)*(-1)^j)*x^(K+j) := by
  have hp := add_pow (-x) (1 : ℝ) n
  rw [show -x+1=1-x by ring] at hp
  simp only [one_pow,mul_one] at hp
  unfold density
  rw [hp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add,neg_pow]
  ring

/-- Exact antiderivative formula, valid at every real endpoint. -/
theorem density_integral_polynomial (K n : ℕ) (x : ℝ) :
    (∫ y : ℝ in (0 : ℝ)..x,density K n y)=
      ((K+n+1).factorial : ℝ)/(K.factorial*n.factorial)*
        ∑ j∈Finset.range (n+1),(n.choose j : ℝ)*(-1)^j*x^(K+j+1)/(K+j+1 : ℕ) := by
  simp_rw [density_sum]
  rw [intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul
      (((K+n+1).factorial : ℝ)/(K.factorial*n.factorial)*(n.choose j : ℝ)*(-1)^j)
      (fun y : ℝ => y^(K+j)),integral_pow]
    simp only [zero_pow (by omega : K+j+1≠0),sub_zero,Nat.cast_add,Nat.cast_one]
    ring
  · intro j _
    exact (by fun_prop : Continuous (fun y : ℝ =>
      (((K+n+1).factorial : ℝ)/(K.factorial*n.factorial)*(n.choose j : ℝ)*(-1)^j)*y^(K+j))).intervalIntegrable _ _

/-- The rational program computes the actual continuous beta CDF exactly. -/
theorem rationalCDF_eq_integral (K n : ℕ) (x : ℚ) :
    (rationalCDF K n x : ℝ)=∫ y : ℝ in (0 : ℝ)..(x : ℝ),density K n y := by
  rw [density_integral_polynomial]
  unfold rationalCDF
  push_cast
  rfl

@[simp] theorem rationalCDF_zero (K n : ℕ) : rationalCDF K n 0=0 := by
  unfold rationalCDF
  have hs : (∑ j∈Finset.range (n+1),(n.choose j : ℚ)*(-1)^j*0^(K+j+1)/(K+j+1 : ℕ))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [show (0 : ℚ)^(K+j+1)=0 from zero_pow (by omega)]
    simp
  rw [hs,mul_zero]

@[simp] theorem rationalCDF_one (K n : ℕ) : rationalCDF K n 1=1 := by
  apply Rat.cast_injective (α:=ℝ)
  rw [rationalCDF_eq_integral]
  simpa only [Rat.cast_one] using density_integral_one K n

/-- Monotonicity, normalization, and rational evaluation are all for the
same CDF, so finite inverse-CDF sampling does not require a real oracle. -/
theorem rationalCDF_mono (K n : ℕ) {x y : ℚ} (hx : 0≤x) (hxy : x≤y) (hy : y≤1) :
    rationalCDF K n x≤rationalCDF K n y := by
  apply (Rat.cast_le (K:=ℝ)).mp
  rw [rationalCDF_eq_integral,rationalCDF_eq_integral]
  apply intervalIntegral.integral_mono_interval (by rfl) (by exact_mod_cast hx) (by exact_mod_cast hxy)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    unfold density
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hz.1.le _))
      (pow_nonneg (sub_nonneg.mpr (hz.2.trans (by exact_mod_cast hy))) _)
  · exact (by unfold density; fun_prop : Continuous _).intervalIntegrable _ _

/-- Every beta density with integer shapes is at most its underlying
order-statistic population, uniformly over the closed unit interval. -/
theorem density_le_population (K n : ℕ) (x : ℝ) (hx : 0≤x) (hx1 : x≤1) :
    density K n x≤K+n+1 := by
  let k : Fin (K+n+1) := ⟨K,by omega⟩
  have hmass : (binomialCount (K+n) x hx hx1).weight k≤1 := by
    rw [← (binomialCount (K+n) x hx hx1).sum_one]
    exact Finset.single_le_sum (fun j _ => (binomialCount (K+n) x hx hx1).nonneg j) (Finset.mem_univ _)
  have he : density K n x=(K+n+1 : ℕ)*(binomialCount (K+n) x hx hx1).weight k := by
    unfold density binomialCount k
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.cast_choose ℝ (by omega : K≤K+n),Nat.add_sub_cancel_left,Nat.factorial_succ]
    push_cast
    field_simp
  rw [he]
  simpa only [mul_one,Nat.cast_add,Nat.cast_one] using
    mul_le_mul_of_nonneg_left hmass (by positivity : (0 : ℝ)≤(K+n+1 : ℕ))

end AFT.BetaReference

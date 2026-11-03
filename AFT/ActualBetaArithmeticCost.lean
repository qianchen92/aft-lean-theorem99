import AFT.ActualBetaNumericalBounds
import AFT.BetaCountedProgram

/-! # Actual finite-beta evaluator: exact law and checked arithmetic work

These are arithmetic-operation bounds for the concrete integer evaluator.
They are accompanied by true binary operand bounds, rather than a claim
that an arbitrary-precision integer operation takes constant bit time.
-/
namespace AFT.V7Calibration
open GaussianSource BetaReference HistogramGenerating
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero
local instance actualBetaArithmeticFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

private theorem actualDimension_positive (n : ℕ) : 0 < Parameters.dimension n := by
  have hi := Parameters.population_identity n
  have hb := Parameters.bodies_positive n
  omega

/-- The counted integer evaluator has exactly the already verified finite
beta law, including its rational fallback on non-typical bins. -/
theorem actualFiniteBetaHistogram_counted_program (C : ℝ) (n : ℕ) :
    actualFiniteBetaHistogram C n=
      (FiniteDist.independent fun _ : Fin (n+n) => FiniteDist.uniform (Fin 2)).mix
        (fun word => actualPositiveReferenceHistogram C n
          ((CountedFraction.beta (Parameters.dimension n) (Parameters.legs n) n (n+n) word).value : ℝ)) := by
  simpa only [CountedFraction.beta_value _ _ _ _ (actualDimension_positive n)] using
    actualFiniteBetaHistogram_integer_program C n

/-- The same executable beta program is used before each genuine zero-charge
conditioning. The histogram target remains the complete histogram. -/
theorem actualFiniteBetaZeroChargeHistogram_counted_program (C : ℝ) (n : ℕ) :
    actualFiniteBetaZeroChargeHistogram C n=
      (FiniteDist.independent fun _ : Fin (n+n) => FiniteDist.uniform (Fin 2)).mix
        (fun word => actualReferenceZeroChargeHistogram C n
          ((CountedFraction.beta (Parameters.dimension n) (Parameters.legs n) n (n+n) word).value : ℝ)) := by
  simpa only [CountedFraction.beta_value _ _ _ _ (actualDimension_positive n)] using
    actualFiniteBetaZeroChargeHistogram_integer_program C n

/-- This includes ticket evaluation, all CDF terms, the binary search,
and the rational typical-value check. The supplied actual public parameters
are the input to the integer evaluator. -/
theorem actual_beta_arithmetic_work (n : ℕ) (hn : 2 ≤ n) (word : Fin (n+n) → Fin 2) :
    (CountedFraction.beta (Parameters.dimension n) (Parameters.legs n) n (n+n) word).work ≤
      100*n^121 := by
  have hpop : Parameters.legs n+(Parameters.dimension n-Parameters.legs n-1)+1=Parameters.dimension n := by
    have hi := Parameters.population_identity n
    have hb := Parameters.bodies_positive n
    omega
  have hN : Parameters.dimension n ≤ 2*n^60 := by
    simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  have hsq : (Parameters.dimension n)^2 ≤ 4*n^120 := by
    have hh := Nat.pow_le_pow_left hN 2
    simpa only [mul_pow,← pow_mul] using hh
  have hmix : n*(Parameters.dimension n)^2 ≤ 4*n^121 := by
    have hh := Nat.mul_le_mul_left n hsq
    simpa only [pow_succ,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using hh
  have hone : 1 ≤ n^121 := Nat.one_le_pow _ _ (by omega)
  have hlinear : n ≤ n^121 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n) (by omega : 1 ≤ 121)
  have hquadratic : n^2 ≤ n^121 :=
    Nat.pow_le_pow_right (by omega : 1 ≤ n) (by omega : 2 ≤ 121)
  have hw := CountedFraction.beta_work_le (Parameters.dimension n) (Parameters.legs n) n (n+n) word
  rw [hpop] at hw
  nlinarith

end
end AFT.V7Calibration

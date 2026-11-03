import AFT.ActualBetaProgram
import AFT.BetaIntegerSampler

/-! # Concrete fair-bit and binary-integer budgets for the V7 beta program -/
namespace AFT.V7Calibration
open GaussianSource BetaReference HistogramGenerating
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero
local instance actualBetaNumericalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The actual reference mixture is also exactly the output of the integer
CDF implementation, followed by its rational typical-value check. -/
theorem actualFiniteBetaHistogram_integer_program (C : ℝ) (n : ℕ) :
    actualFiniteBetaHistogram C n=
      (FiniteDist.independent fun _ : Fin (n+n) => FiniteDist.uniform (Fin 2)).mix
        (fun word => actualPositiveReferenceHistogram C n
          (integerSafeDraw (Parameters.dimension n) (Parameters.legs n) n (n+n) word : ℝ)) := by
  simpa only [integerSafeDraw_eq_safeFiniteDraw] using actualFiniteBetaHistogram_fair_bits C n

theorem actualFiniteBetaZeroChargeHistogram_integer_program (C : ℝ) (n : ℕ) :
    actualFiniteBetaZeroChargeHistogram C n=
      (FiniteDist.independent fun _ : Fin (n+n) => FiniteDist.uniform (Fin 2)).mix
        (fun word => actualReferenceZeroChargeHistogram C n
          (integerSafeDraw (Parameters.dimension n) (Parameters.legs n) n (n+n) word : ℝ)) := by
  simpa only [integerSafeDraw_eq_safeFiniteDraw] using actualFiniteBetaZeroChargeHistogram_fair_bits C n

/-- All actual partial CDF numerator sums, complete denominators, and
scaled ticket numerators have a fixed polynomial bound on their true binary
length. This includes queries at either endpoint. -/
theorem actual_beta_integer_sizes (n : ℕ) (hn : 2 ≤ n) (a length : ℕ)
    (ha : a ≤ 2^n) (hl : length ≤ Parameters.dimension n-Parameters.legs n-1+1) :
    (integerCDFPrefix (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1)
      (2^n) a length).natAbs.size ≤ 32*n^120 ∧
    (integerCDFDenominator (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) (2^n)).size ≤ 32*n^120 ∧
    (2^(n+n)*(integerCDFNumerator (Parameters.legs n)
      (Parameters.dimension n-Parameters.legs n-1) (2^n) a).toNat).size ≤ 32*n^120 := by
  have hpop : Parameters.legs n+(Parameters.dimension n-Parameters.legs n-1)+1=Parameters.dimension n := by
    have hi := Parameters.population_identity n
    have hb := Parameters.bodies_positive n
    omega
  have hN : Parameters.dimension n ≤ 2*n^60 := by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  have hp := integerCDFPrefix_bitSize (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) n a length ha hl
  have hd := integerCDFDenominator_bitSize (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) n
  have ht := integerTicketNumerator_bitSize (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) n (n+n) a ha
  rw [hpop] at hp hd ht
  have hsq : (Parameters.dimension n)^2 ≤ 4*n^120 := by
    have hh := Nat.pow_le_pow_left hN 2
    simpa only [mul_pow,← pow_mul] using hh
  have hn60 : n ≤ n^60 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n) (by omega : 1 ≤ 60)
  have hn120 : n ≤ n^120 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n) (by omega : 1 ≤ 120)
  have hmix : n*Parameters.dimension n ≤ 2*n^120 := by
    have hh := Nat.mul_le_mul hn60 hN
    simpa only [← pow_add,show (60+60 : ℕ)=120 from rfl,Nat.mul_left_comm] using hh
  have hone : 1 ≤ n^120 := Nat.one_le_pow _ _ (by omega)
  exact ⟨hp.trans (by omega),hd.trans (by omega),ht.trans (by omega)⟩

/-- Across all `n` actual CDF queries, there are at most `2 n^61`
polynomial summands to evaluate, rather than an enumeration of `2^n` bins. -/
theorem actual_beta_polynomial_terms (n : ℕ) (hn : 2 ≤ n) :
    n*(Parameters.dimension n-Parameters.legs n-1+1) ≤ 2*n^61 := by
  have hN : Parameters.dimension n ≤ 2*n^60 := by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  have hlen : Parameters.dimension n-Parameters.legs n-1+1 ≤ Parameters.dimension n := by
    have hi := Parameters.population_identity n
    have hb := Parameters.bodies_positive n
    have hK : 0 < Parameters.legs n := by unfold Parameters.legs; have := Parameters.security_ge_two n; positivity
    omega
  calc
    _ ≤ n*(2*n^60) := Nat.mul_le_mul_left n (hlen.trans hN)
    _ = _ := by rw [pow_succ]; ring

end
end AFT.V7Calibration

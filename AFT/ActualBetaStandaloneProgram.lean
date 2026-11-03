import AFT.ActualBetaArithmeticCost
import AFT.ParameterProgram

/-! # A standalone beta program from the security parameter and fair bits

The executable definition includes the bounded prime search and the actual
V7 population powers. No public modulus, beta sample, or real-number oracle
is supplied as an extra input.
-/
namespace AFT.ParameterProgram
open BetaReference

/-- All values used by the beta evaluator are produced by this finite
integer program. The only random input is the displayed `2 n` fair bits. -/
def beta (parameter : ℕ) (word : Fin (parameter+parameter) → Fin 2) : CountedFraction :=
  let prime := modulus parameter
  let density := CountedInteger.power ((max 2 parameter : ℕ) : ℤ) 20
  let legs := CountedInteger.power ((max 2 parameter : ℕ) : ℤ) 30
  let population := prime.value*density.value.toNat
  let result := CountedFraction.beta population legs.value.toNat parameter (parameter+parameter) word
  ⟨result.numerator,result.denominator,prime.work+density.work+legs.work+result.work+3⟩

private theorem power_security_toNat (parameter exponent : ℕ) :
    (CountedInteger.power ((max 2 parameter : ℕ) : ℤ) exponent).value.toNat=
      Parameters.security parameter^exponent := by
  rw [CountedInteger.power_value,← Nat.cast_pow,Int.toNat_natCast]
  rfl

theorem beta_value (parameter : ℕ) (word : Fin (parameter+parameter) → Fin 2) :
    (beta parameter word).value=
      (CountedFraction.beta (Parameters.dimension parameter) (Parameters.legs parameter)
        parameter (parameter+parameter) word).value := by
  simp only [beta,CountedFraction.value,modulus_value,power_security_toNat,
    Parameters.dimension,Parameters.meanDensity,Parameters.legs]

theorem beta_work_le (parameter : ℕ) (hparameter : 2 ≤ parameter)
    (word : Fin (parameter+parameter) → Fin 2) :
    (beta parameter word).work ≤ 300*parameter^121 := by
  have hp := modulus_work_le parameter
  have hb := V7Calibration.actual_beta_arithmetic_work parameter hparameter word
  have hpow : parameter^80 ≤ parameter^121 :=
    Nat.pow_le_pow_right (by omega : 1 ≤ parameter) (by omega : 80 ≤ 121)
  have hone : 1 ≤ parameter^121 := Nat.one_le_pow _ _ (by omega)
  rw [Parameters.security_eq parameter hparameter] at hp
  simp only [beta,CountedInteger.power_work,modulus_value,power_security_toNat]
  change (modulus parameter).work+20+30+
    (CountedFraction.beta (Parameters.dimension parameter) (Parameters.legs parameter)
      parameter (parameter+parameter) word).work+3 ≤ _
  omega

end AFT.ParameterProgram

namespace AFT.V7Calibration
open GaussianSource BetaReference HistogramGenerating
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero
local instance actualBetaStandaloneFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- Exact linkage of the full standalone program with the previously
proved complete reference histogram mixture. -/
theorem actualFiniteBetaHistogram_standalone_program (C : ℝ) (n : ℕ) :
    actualFiniteBetaHistogram C n=
      (FiniteDist.independent fun _ : Fin (n+n) => FiniteDist.uniform (Fin 2)).mix
        (fun word => actualPositiveReferenceHistogram C n ((ParameterProgram.beta n word).value : ℝ)) := by
  simpa only [ParameterProgram.beta_value] using actualFiniteBetaHistogram_counted_program C n

theorem actualFiniteBetaZeroChargeHistogram_standalone_program (C : ℝ) (n : ℕ) :
    actualFiniteBetaZeroChargeHistogram C n=
      (FiniteDist.independent fun _ : Fin (n+n) => FiniteDist.uniform (Fin 2)).mix
        (fun word => actualReferenceZeroChargeHistogram C n ((ParameterProgram.beta n word).value : ℝ)) := by
  simpa only [ParameterProgram.beta_value] using actualFiniteBetaZeroChargeHistogram_counted_program C n

end
end AFT.V7Calibration

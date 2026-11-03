import AFT.ActualBodyCenterProgram
import AFT.ActualTripleEnergy
import AFT.ActualPairedMatrixProgram

/-! # Rational evaluation of the actual integer shifted compensated body -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- This uses integer equality, retaining the physical palette boundary. -/
def actualShiftedBodyProgram (constant n : ℕ) (beta : ℚ) (shift : ℤ) (output : ℕ) : ℚ :=
  ∑ center∈Finset.range (ParameterProgram.modulus n).value,
    if (output : ℤ)=(center : ℤ)+shift then actualBodyCenterProgram constant n beta center else 0

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance shiftedBodyProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualShiftedBodyProgramError (n : ℕ) : ℝ := 2*(n : ℝ)^40*actualBodyCenterProgramError n

theorem actualShiftedBodyProgramError_negligible : Negligible actualShiftedBodyProgramError := by
  convert (actualBodyCenterProgramError_negligible.mul_polynomial 40).const_mul 2 using 1
  funext n;unfold actualShiftedBodyProgramError;ring

/-- Uniformity includes every legal root, source, queue and output. -/
theorem actual_shifted_body_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ (shift : ℤ) (output : Fin (Parameters.modulus n)),
      |shift| ≤ (maxBodyShift constant n : ℤ) →
      |(actualShiftedBodyProgram constant n (beta n) shift output.val : ℝ)-
        (actualShiftedBodyLaw constant n (beta n) shift).weight output| ≤ actualShiftedBodyProgramError n := by
  filter_upwards [actual_body_center_program_eventually constant hc beta hbeta,
    actual_shifted_body_law_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    eventually_ge_atTop 2] with n hp hs hn shift output hshift
  have he : 0 ≤ actualBodyCenterProgramError n := (abs_nonneg _).trans (hp ⟨0,(Parameters.modulus_prime n).pos⟩)
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  rw [(hs shift hshift).1]
  simp only [actualShiftedBodyProgram,Rat.cast_sum,apply_ite,Rat.cast_zero,ParameterProgram.modulus_value]
  rw [←Fin.sum_univ_eq_sum_range]
  unfold integerShiftProfile
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _center : Fin (Parameters.modulus n),actualBodyCenterProgramError n := by
      apply Finset.sum_le_sum
      intro center _
      split_ifs
      · exact hp center
      · simpa only [sub_self,abs_zero] using he
    _ = (Parameters.modulus n : ℝ)*actualBodyCenterProgramError n := by simp
    _ ≤ actualShiftedBodyProgramError n := mul_le_mul_of_nonneg_right hq he

/-- Clipping is a computable convenience and does not enlarge the error. -/
theorem actual_shifted_body_clamp_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ (shift : ℤ) (output : Fin (Parameters.modulus n)),
      |shift| ≤ (maxBodyShift constant n : ℤ) →
      |(probabilityClamp (actualShiftedBodyProgram constant n (beta n) shift output.val) : ℝ)-
        (actualShiftedBodyLaw constant n (beta n) shift).weight output| ≤ actualShiftedBodyProgramError n := by
  filter_upwards [actual_shifted_body_program_eventually constant hc beta hbeta] with n hh shift output hs
  exact (probabilityClamp_error _ _ ((actualShiftedBodyLaw constant n (beta n) shift).nonneg output)
    ((actualShiftedBodyLaw constant n (beta n) shift).atom_le_one output)).trans (hh shift output hs)

end
end AFT.V7Calibration

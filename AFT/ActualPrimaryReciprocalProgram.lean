import AFT.ActualPairedMatrixProgram
import AFT.PrimaryLawLower

/-! # A stable rational reciprocal of every actual primary probability -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualPrimaryReciprocalProgram (constant n : ℕ) (beta : ℚ) (color : ℕ) : ℚ :=
  (max (actualPrimaryProgram constant n beta color) (1/(8*(ParameterProgram.modulus n).value : ℚ)))⁻¹

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance primaryReciprocalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualPrimaryReciprocalProgramError (n : ℕ) : ℝ :=
  256*(n : ℝ)^80*actualPrimaryProgramError n

theorem actualPrimaryReciprocalProgramError_negligible : Negligible actualPrimaryReciprocalProgramError := by
  convert (actualPrimaryProgramError_negligible.mul_polynomial 80).const_mul 256 using 1
  funext n
  unfold actualPrimaryReciprocalProgramError
  ring

theorem actual_primary_reciprocal_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ color : Fin (Parameters.modulus n),
      0 < (actualPrimaryReciprocalProgram constant n (beta n) color.val : ℝ) ∧
      (actualPrimaryReciprocalProgram constant n (beta n) color.val : ℝ) ≤ 16*(n : ℝ)^40 ∧
      |(actualPrimaryReciprocalProgram constant n (beta n) color.val : ℝ)-
        ((actualPrimaryLaw constant n (beta n)).weight color)⁻¹| ≤ actualPrimaryReciprocalProgramError n := by
  filter_upwards [actual_primary_program_eventually constant hc,
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    actual_reference_laws_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    hbeta,eventually_ge_atTop 2] with n happ hlower hl hb hn color
  have hq : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hqbound : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hlo : 0 < 1/(8*(Parameters.modulus n : ℝ)) := by positivity
  have hlow : 1/(8*(Parameters.modulus n : ℝ)) ≤ (actualPrimaryLaw constant n (beta n)).weight color := by
    apply le_trans _ (hlower color)
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have he : |(actualPrimaryProgram constant n (beta n) color.val : ℝ)-
      (actualPrimaryLaw constant n (beta n)).weight color| ≤ actualPrimaryProgramError n := by
    rw [hl.1]
    exact happ (beta n) hb.1 color
  have hen : 0 ≤ actualPrimaryProgramError n := (abs_nonneg _).trans he
  simp only [actualPrimaryReciprocalProgram,Rat.cast_inv,Rat.cast_max,Rat.cast_div,Rat.cast_one,
    Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,ParameterProgram.modulus_value]
  have hm : 0 < max (actualPrimaryProgram constant n (beta n) color.val : ℝ) (1/(8*Parameters.modulus n)) :=
    hlo.trans_le (le_max_right _ _)
  refine ⟨inv_pos.mpr hm,?_,?_⟩
  · have hh := one_div_le_one_div_of_le hlo (le_max_right (actualPrimaryProgram constant n (beta n) color.val : ℝ) _)
    simp only [one_div,inv_inv] at hh
    simpa only [one_div] using hh.trans (show 8*(Parameters.modulus n : ℝ) ≤ 16*(n : ℝ)^40 by nlinarith)
  · apply (clippedInverse_error _ _ _ hlo hlow).trans
    calc
      _ ≤ actualPrimaryProgramError n/(1/(8*(Parameters.modulus n : ℝ)))^2 :=
        div_le_div_of_nonneg_right he (sq_nonneg _)
      _ = 64*(Parameters.modulus n : ℝ)^2*actualPrimaryProgramError n := by field_simp;ring
      _ ≤ actualPrimaryReciprocalProgramError n := by
        unfold actualPrimaryReciprocalProgramError
        have hq2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Parameters.modulus n) hqbound 2
        have hh := mul_le_mul_of_nonneg_right hq2 hen
        nlinarith [show ((2*(n : ℝ)^40)^2)=4*(n : ℝ)^80 by ring]

end
end AFT.V7Calibration

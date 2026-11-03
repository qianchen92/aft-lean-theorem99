import AFT.ActualInteriorMassProgram
import AFT.NumericalMatrixComposition
import AFT.ActualResponseProgram

/-! # The actual primary boundary collapse as an executable density matrix -/
namespace AFT.RationalNumerics
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color] [DecidableEq Color]

def boundaryDensityEntry (interior : Finset Color) (primary : Color → ℝ) (input output : Color) : ℝ :=
  if output∈interior then if input∈interior then primary input/(∑ color∈interior,primary color) else 0
  else if output=input then 1 else 0

/-- Zero and boundary branches are exact, with no convention at a missing
reference atom: the actual primary reference is strictly positive. -/
theorem boundaryDensityEntry_eq (interior : Finset Color) (primary : Color → ℝ)
    (hp : ∀ color,primary color≠0) (input output : Color) :
    boundaryDensityEntry interior primary input output=
      densityMatrixEntry primary (boundaryCollapse interior primary) input output := by
  cases Subsingleton.elim (inferInstance : DecidableEq Color) (Classical.decEq Color)
  unfold boundaryDensityEntry densityMatrixEntry
  rw [LinearMap.toMatrix'_apply]
  by_cases ho : output∈interior
  · rw [if_pos ho,boundaryCollapse_interior _ _ _ _ ho]
    simp only [Pi.single_apply,Finset.sum_ite_eq']
    by_cases hi : input∈interior
    · simp only [if_pos hi]
      field_simp [hp output]
    · simp only [if_neg hi,zero_mul,mul_zero,zero_div]
  · rw [if_neg ho,boundaryCollapse_boundary _ _ _ _ ho]
    by_cases hi : output=input
    · subst output
      simp only [if_true,Pi.single_eq_same,mul_one,div_self (hp input)]
    · simp only [Pi.single_apply,hi,if_false,mul_zero,zero_div]

end
end AFT.RationalNumerics

namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualBoundaryDensityProgram (constant n : ℕ) (beta : ℚ) (input output : ℕ) : ℚ :=
  if actualInteriorTest constant n output then
    if actualInteriorTest constant n input then
      probabilityClamp (actualPrimaryProgram constant n beta input)*actualInteriorReciprocalProgram constant n beta
    else 0
  else if output=input then 1 else 0

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000
local instance boundaryDensityProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualBoundaryDensityProgramError (n : ℕ) : ℝ :=
  8*(n : ℝ)^40*actualPrimaryProgramError n+actualInteriorReciprocalProgramError n

theorem actualBoundaryDensityProgramError_negligible : Negligible actualBoundaryDensityProgramError := by
  convert ((actualPrimaryProgramError_negligible.mul_polynomial 40).const_mul 8).add
    actualInteriorReciprocalProgramError_negligible using 1
  funext n;unfold actualBoundaryDensityProgramError;ring

theorem actual_boundary_density_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ input output : Fin (Parameters.modulus n),
      let exactEntry := boundaryDensityEntry (boundaryPalette (Parameters.modulus n)
        (boundaryHalf (constant : ℝ) n))ᶜ (actualPrimaryLaw constant n (beta n)).weight input output
      |exactEntry| ≤ 17*(n : ℝ)^40 ∧
      |(actualBoundaryDensityProgram constant n (beta n) input.val output.val : ℝ)| ≤ 17*(n : ℝ)^40 ∧
      |(actualBoundaryDensityProgram constant n (beta n) input.val output.val : ℝ)-exactEntry| ≤
        actualBoundaryDensityProgramError n := by
  filter_upwards [actual_interior_mass_program_eventually constant hc beta hbeta,
    actual_interior_reciprocal_program_eventually constant hc beta hbeta,
    actual_primary_program_eventually constant hc,
    actual_reference_laws_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    hbeta,eventually_ge_atTop 2] with n hm hr hp hl hb hn input output
  have hq0 : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn40 : 1 ≤ (n : ℝ)^40 := one_le_pow₀ hn1
  have hp0 : 0 ≤ (actualPrimaryLaw constant n (beta n)).weight input := (actualPrimaryLaw constant n (beta n)).nonneg input
  have hp1 : (actualPrimaryLaw constant n (beta n)).weight input ≤ 1 := by
    simpa only [(actualPrimaryLaw constant n (beta n)).sum_one] using Finset.single_le_sum
      (fun color (_ : color∈Finset.univ) => (actualPrimaryLaw constant n (beta n)).nonneg color) (Finset.mem_univ input)
  have hpa := probabilityClamp_bounds (actualPrimaryProgram constant n (beta n) input.val)
  have hpe : |(probabilityClamp (actualPrimaryProgram constant n (beta n) input.val) : ℝ)-
      (actualPrimaryLaw constant n (beta n)).weight input| ≤ actualPrimaryProgramError n := by
    apply (probabilityClamp_error _ _ hp0 hp1).trans
    rw [hl.1]
    exact hp (beta n) hb.1 input
  have hm0 : 0 < actualInteriorMass constant n (beta n) := (by positivity : (0 : ℝ)<1/(4*(Parameters.modulus n : ℝ))).trans_le hm.1
  have hmi : (actualInteriorMass constant n (beta n))⁻¹ ≤ 8*(n : ℝ)^40 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0<1/(4*(Parameters.modulus n : ℝ))) hm.1
    simp only [one_div,inv_inv] at hh
    exact hh.trans (by linarith)
  have he0 : 0 ≤ actualPrimaryProgramError n := (abs_nonneg _).trans hpe
  have hr0 : 0 ≤ actualInteriorReciprocalProgramError n := (abs_nonneg _).trans hr.2.2
  have hE0 : 0 ≤ actualBoundaryDensityProgramError n := by unfold actualBoundaryDensityProgramError;positivity
  have hprog : (actualBoundaryDensityProgram constant n (beta n) input.val output.val : ℝ)=
      if output∈(boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n))ᶜ then
        if input∈(boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n))ᶜ then
          (probabilityClamp (actualPrimaryProgram constant n (beta n) input.val) : ℝ)*
            (actualInteriorReciprocalProgram constant n (beta n) : ℝ) else 0
      else if output=input then 1 else 0 := by
    unfold actualBoundaryDensityProgram
    rw [actualInteriorTest_eq,actualInteriorTest_eq]
    by_cases ho : output∈(boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n))ᶜ
    · by_cases hi : input∈(boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n))ᶜ <;>
        simp only [ho,hi,decide_true,decide_false,Bool.false_eq_true,if_true,if_false,Rat.cast_mul,Rat.cast_zero]
    · by_cases heq : output=input
      · subst output
        simp only [ho,decide_false,Bool.false_eq_true,if_false,ite_true,Rat.cast_one]
      · have hne : output.val≠input.val := fun h => heq (Fin.ext h)
        simp only [ho,hne,heq,decide_false,Bool.false_eq_true,if_false,Rat.cast_zero]
  dsimp only
  rw [hprog]
  unfold boundaryDensityEntry
  split_ifs with ho hi heq
  · change |(actualPrimaryLaw constant n (beta n)).weight input/actualInteriorMass constant n (beta n)| ≤ _ ∧
      |(probabilityClamp (actualPrimaryProgram constant n (beta n) input.val) : ℝ)*
        (actualInteriorReciprocalProgram constant n (beta n) : ℝ)| ≤ _ ∧ _
    refine ⟨?_,?_,?_⟩
    · rw [div_eq_mul_inv,abs_mul,abs_of_nonneg hp0,abs_of_pos (inv_pos.mpr hm0)]
      exact (mul_le_mul hp1 hmi (by positivity) (by norm_num)).trans (by nlinarith only [hn40])
    · rw [abs_mul,abs_of_nonneg hpa.1,abs_of_pos hr.1]
      exact (mul_le_mul hpa.2 hr.2.1 hr.1.le (by norm_num)).trans (by nlinarith only [hn40])
    · change |(probabilityClamp (actualPrimaryProgram constant n (beta n) input.val) : ℝ)*
          (actualInteriorReciprocalProgram constant n (beta n) : ℝ)-
          (actualPrimaryLaw constant n (beta n)).weight input/actualInteriorMass constant n (beta n)| ≤ _
      rw [div_eq_mul_inv]
      apply (approximation_mul_error _ _ _ _).trans
      rw [abs_of_pos (inv_pos.mpr hm0),abs_of_nonneg hpa.1]
      exact (add_le_add (mul_le_mul hpe hmi (by positivity) he0)
        (mul_le_mul hpa.2 hr.2.2 (abs_nonneg _) (by norm_num))).trans_eq (by
          unfold actualBoundaryDensityProgramError;ring)
  all_goals norm_num [hE0]
  all_goals nlinarith only [hn40]

end
end AFT.V7Calibration

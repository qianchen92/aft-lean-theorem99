import AFT.ActualDensityInverseBounds
import AFT.NumericalMatrixComposition

/-! # The density inverse without the activation rescaling -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualUnactivatedInverseProgram (constant n : ℕ) (beta : ℚ) (input output : ℕ) : ℚ :=
  probabilityClamp (actualActivationApprox constant n n)*actualDensityInverseProgram constant n beta input output

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000
local instance unactivatedInverseProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualUnactivatedInverseProgramError (n : ℕ) : ℝ :=
  257*(n : ℝ)^120*(1/(2 : ℝ)^n)+actualDensityInverseProgramError n

theorem actualUnactivatedInverseProgramError_negligible : Negligible actualUnactivatedInverseProgramError := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n;simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  convert ((hm.mul_polynomial 120).const_mul 257).add actualDensityInverseProgramError_negligible using 1
  funext n;unfold actualUnactivatedInverseProgramError;ring

theorem actual_unactivated_inverse_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse (constant : ℝ) n →∀ input output,
      |densityMatrixEntry (actualPrimaryLaw constant n (beta n)).weight operator.symm.toLinearMap input output| ≤ 257*(n : ℝ)^120 ∧
      |(actualUnactivatedInverseProgram constant n (beta n) input.val output.val : ℝ)| ≤ 257*(n : ℝ)^120 ∧
      |(actualUnactivatedInverseProgram constant n (beta n) input.val output.val : ℝ)-
        densityMatrixEntry (actualPrimaryLaw constant n (beta n)).weight operator.symm.toLinearMap input output| ≤
        actualUnactivatedInverseProgramError n := by
  filter_upwards [actual_density_inverse_estimates_eventually constant hc beta hbeta,eventually_ge_atTop 2]
    with n hi hn operator hop input output
  have hρ : 0 < v7Activation constant n := activation_positive _ _ _ _
    (legFeatureCount_positive (constant : ℝ) n (by exact_mod_cast hc) (by omega))
  have hρ1 : v7Activation constant n ≤ 1 := activation_le_one _ _ _ _
  have ha := probabilityClamp_bounds (actualActivationApprox constant n n)
  have he := (probabilityClamp_error (actualActivationApprox constant n n) (v7Activation constant n) hρ.le hρ1).trans
    (actualActivationApprox_error constant n n hc (by omega))
  have hi := hi operator hop input output
  have hexact : densityMatrixEntry (actualPrimaryLaw constant n (beta n)).weight operator.symm.toLinearMap input output=
      v7Activation constant n*actualDensityInverseEntry constant n (beta n) operator input output := by
    unfold densityMatrixEntry actualDensityInverseEntry
    rw [LinearMap.toMatrix'_apply]
    field_simp [hρ.ne']
    rfl
  rw [hexact]
  simp only [actualUnactivatedInverseProgram,Rat.cast_mul]
  refine ⟨?_,?_,?_⟩
  · rw [abs_mul,abs_of_pos hρ]
    exact (mul_le_mul hρ1 hi.1 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · rw [abs_mul,abs_of_nonneg ha.1]
    exact (mul_le_mul ha.2 hi.2.1 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · apply (approximation_mul_error _ _ _ _).trans
    rw [abs_of_nonneg ha.1]
    exact (add_le_add (mul_le_mul he hi.1 (abs_nonneg _) (by positivity))
      (mul_le_mul ha.2 hi.2.2 (abs_nonneg _) (by norm_num))).trans_eq (by
        unfold actualUnactivatedInverseProgramError;ring)

end
end AFT.V7Calibration

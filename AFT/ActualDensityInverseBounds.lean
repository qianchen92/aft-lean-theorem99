import AFT.ActualDensityInverseProgram

/-! # Polynomial magnitude bounds for the computed density inverse -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000
local instance densityInverseBoundsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualDensityInverseEntry (constant : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (input output : Fin (Parameters.modulus n)) : ℝ :=
  (v7Activation constant n)⁻¹*(actualPrimaryLaw constant n beta).weight input*
    operator.symm (Pi.single input 1) output/(actualPrimaryLaw constant n beta).weight output

/-- Both the exact entry and its actual rational approximation are bounded
by one fixed polynomial, uniformly over the entire primary palette. -/
theorem actual_density_inverse_estimates_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse (constant : ℝ) n →∀ input output,
      |actualDensityInverseEntry constant n (beta n) operator input output| ≤ 257*(n : ℝ)^120 ∧
      |(actualDensityInverseProgram constant n (beta n) input.val output.val : ℝ)| ≤ 257*(n : ℝ)^120 ∧
      |(actualDensityInverseProgram constant n (beta n) input.val output.val : ℝ)-
        actualDensityInverseEntry constant n (beta n) operator input output| ≤ actualDensityInverseProgramError n := by
  filter_upwards [actual_density_inverse_program_eventually constant hc beta hbeta,
    actual_inverse_entry_bound_eventually constant hc,
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    v7Activation_lower_eventually (constant : ℝ) (by exact_mod_cast hc),
    actualDensityInverseProgramError_negligible 0,eventually_ge_atTop 2]
    with n happ hinv hlower hrho hsmall hn operator hop input output
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hq0 : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hrho0 : 0 < v7Activation constant n := lt_of_lt_of_le (by positivity) hrho
  have hrhoi : |(v7Activation constant n)⁻¹| ≤ (n : ℝ)^5 := by
    rw [abs_of_pos (inv_pos.mpr hrho0)]
    have hh := one_div_le_one_div_of_le (by positivity : 0 < ((n : ℝ)^5)⁻¹) hrho
    simpa only [one_div,inv_inv] using hh
  have hp : |(actualPrimaryLaw constant n (beta n)).weight input| ≤ 1 := by
    rw [abs_of_nonneg ((actualPrimaryLaw constant n (beta n)).nonneg input)]
    simpa only [(actualPrimaryLaw constant n (beta n)).sum_one] using Finset.single_le_sum
      (fun color (_ : color∈Finset.univ) => (actualPrimaryLaw constant n (beta n)).nonneg color) (Finset.mem_univ input)
  have hpo : 0 < (actualPrimaryLaw constant n (beta n)).weight output :=
    lt_of_lt_of_le (by positivity) (hlower output)
  have hpi : |((actualPrimaryLaw constant n (beta n)).weight output)⁻¹| ≤ 8*(n : ℝ)^40 := by
    rw [abs_of_pos (inv_pos.mpr hpo)]
    have hh := one_div_le_one_div_of_le (by positivity : 0 < 1/(4*(Parameters.modulus n : ℝ))) (hlower output)
    simp only [one_div,inv_inv] at hh
    exact hh.trans (by linarith)
  have hx : |actualDensityInverseEntry constant n (beta n) operator input output| ≤ 256*(n : ℝ)^120 := by
    unfold actualDensityInverseEntry
    rw [div_eq_mul_inv,abs_mul,abs_mul,abs_mul]
    calc
      _ ≤ ((n : ℝ)^5*1)*(32*(n : ℝ)^70)*(8*(n : ℝ)^40) := by
        exact mul_le_mul (mul_le_mul (mul_le_mul hrhoi hp (abs_nonneg _) (by positivity))
          (hinv operator hop input output) (abs_nonneg _) (by positivity)) hpi (abs_nonneg _) (by positivity)
      _ = 256*(n : ℝ)^115 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by decide : 115 ≤ 120)) (by norm_num)
  have he := happ operator hop input output
  change |_ - actualDensityInverseEntry constant n (beta n) operator input output| ≤ _ at he
  have he1 : actualDensityInverseProgramError n ≤ 1 := by
    simpa only [pow_zero,div_one] using (le_abs_self _).trans hsmall
  have hn120 : 1 ≤ (n : ℝ)^120 := one_le_pow₀ hn1
  refine ⟨hx.trans (by nlinarith only [hn120]),?_,he⟩
  have hh := abs_add_le
    ((actualDensityInverseProgram constant n (beta n) input.val output.val : ℝ)-
      actualDensityInverseEntry constant n (beta n) operator input output)
    (actualDensityInverseEntry constant n (beta n) operator input output)
  rw [sub_add_cancel] at hh
  nlinarith only [hh,he,he1,hx,hn120]

end
end AFT.V7Calibration

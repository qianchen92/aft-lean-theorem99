import AFT.BetaGridParameters

/-! # Actual V7 beta grid errors are negligible at fixed finite precision -/
namespace AFT.V7Calibration
open GaussianSource BetaReference Filter
open scoped Topology
noncomputable section

def actualBetaGridError (C : ℝ) (n : ℕ) : ℝ :=
  2*Parameters.legs n*actualBoundaryFraction C n/((betaGridCutoff n)^2*(2^n : ℕ))

theorem actual_beta_mesh_typical_eventually :
    ∀ᶠ n in atTop,betaGridMesh n ≤ (Parameters.legs n : ℝ)/(2*Parameters.dimension n) := by
  filter_upwards [betaGridMesh_negligible 62,eventually_ge_atTop 2] with n hm hn
  rw [abs_of_nonneg (by unfold betaGridMesh; positivity)] at hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (Parameters.dimension n : ℝ) ≤ 2*(n : ℝ)^60 := by exact_mod_cast
    (by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2)
  have hNp : (0 : ℝ) < Parameters.dimension n := by
    have hi := Parameters.population_identity n
    have hb := Parameters.bodies_positive n
    exact_mod_cast (by omega : 0 < Parameters.dimension n)
  have hK : (1 : ℝ) ≤ Parameters.legs n := by
    unfold Parameters.legs
    exact_mod_cast (Nat.one_le_pow 30 (Parameters.security n) (by have := Parameters.security_ge_two n; omega))
  calc
    _ ≤ 1/(n : ℝ)^62 := hm
    _ ≤ 1/(4*(n : ℝ)^60) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [show (62 : ℕ)=60+2 by norm_num,pow_add]
      nlinarith [mul_le_mul_of_nonneg_left (show (4 : ℝ) ≤ (n : ℝ)^2 by nlinarith) (pow_nonneg hn0.le 60)]
    _ ≤ _ := div_le_div₀ (by norm_num) hK (by positivity) (by linarith)

theorem actual_beta_grid_error_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,0 ≤ actualBetaGridError C n ∧
      actualBetaGridError C n ≤ 4*(n : ℝ)^124*betaGridMesh n := by
  filter_upwards [beta_grid_legal_eventually C hC,actual_beta_cutoff_eventually C hC,eventually_ge_atTop 2]
    with n hg hc hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : (Parameters.dimension n : ℝ) ≤ 2*(n : ℝ)^60 := by exact_mod_cast
    (by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2)
  have hK : (Parameters.legs n : ℝ) ≤ Parameters.dimension n := by
    have hi := Parameters.population_identity n
    exact_mod_cast (by omega : Parameters.legs n ≤ Parameters.dimension n)
  have hb0 : 0 ≤ actualBoundaryFraction C n := by unfold actualBoundaryFraction; positivity
  have hb1 : actualBoundaryFraction C n ≤ 1 := hc.2.1.trans hc.2.2.2.le
  have hnum : 2*(Parameters.legs n : ℝ)*actualBoundaryFraction C n ≤ 4*(n : ℝ)^60 := by
    calc
      _ ≤ 2*(Parameters.legs n : ℝ)*1 := mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ ≤ 4*(n : ℝ)^60 := by linarith
  have hden : (1/(n : ℝ)^32)^2*(2^n : ℕ) ≤ (betaGridCutoff n)^2*(2^n : ℕ) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hg.2.2.2.1 2) (by positivity)
  refine ⟨by unfold actualBetaGridError; positivity,?_⟩
  calc
    _ ≤ (4*(n : ℝ)^60)/((1/(n : ℝ)^32)^2*(2^n : ℕ)) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = _ := by unfold betaGridMesh; field_simp

theorem actualBetaGridError_negligible (C : ℝ) (hC : 1 ≤ C) : Negligible (actualBetaGridError C) := by
  have hh := (betaGridMesh_negligible.mul_polynomial 124).const_mul 4
  apply hh.of_eventually_le
  filter_upwards [actual_beta_grid_error_eventually C hC] with n hn
  rw [abs_of_nonneg hn.1,abs_of_nonneg (by unfold betaGridMesh; positivity)]
  simpa only [mul_assoc] using hn.2

end
end AFT.V7Calibration

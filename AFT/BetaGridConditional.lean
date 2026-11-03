import AFT.BetaQuadrature
import AFT.MixtureConditioning

/-! # Exact retained grid beta laws -/
namespace AFT.BetaReference
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem sum_fin_tail (M J : ℕ) (f : ℕ → ℝ) :
    (∑ j : Fin M,if J ≤ j.val then f j.val else 0)=∑ j ∈ Finset.Ico J M,f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if J ≤ j then f j else 0),← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  · intro j _
    rfl

theorem gridLaw_tail_mass (K n M J : ℕ) (hM : 0 < M) (hJM : J ≤ M) :
    (gridLaw K n M hM).eventMass (fun j => J ≤ j.val)=
      ∫ x : ℝ in (J : ℝ)/M..1,density K n x := by
  have hsum : (gridLaw K n M hM).eventMass (fun j => J ≤ j.val)=
      ∑ j ∈ Finset.Ico J M,((gridCDF K n M (j+1)-gridCDF K n M j : ℚ) : ℝ) := by
    simp only [FiniteDist.eventMass,gridLaw]
    convert sum_fin_tail M J (fun j => ((gridCDF K n M (j+1)-gridCDF K n M j : ℚ) : ℝ)) using 1
  rw [hsum]
  simp only [Rat.cast_sub]
  rw [Finset.sum_Ico_eq_sub _ hJM,Finset.sum_range_sub (fun j => (gridCDF K n M j : ℝ)) M,
    Finset.sum_range_sub (fun j => (gridCDF K n M j : ℝ)) J]
  simp only [gridCDF_total K n M hM,gridCDF_zero,Rat.cast_one,Rat.cast_zero,sub_zero]
  have hi : Continuous (density K n) := by unfold density; fun_prop
  have he := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hi.intervalIntegrable 0 ((J : ℝ)/M)) (hi.intervalIntegrable ((J : ℝ)/M) 1)
  rw [density_integral_one] at he
  have hj := rationalCDF_eq_integral K n ((J : ℚ)/M)
  simp only [Rat.cast_div,Rat.cast_natCast] at hj
  change 1-((rationalCDF K n ((J : ℚ)/M)) : ℝ)=_
  linarith

theorem gridLaw_tail_positive (K n M J : ℕ) (hM : 0 < M) (hJM : J < M) :
    0 < (gridLaw K n M hM).eventMass (fun j => J ≤ j.val) := by
  rw [gridLaw_tail_mass K n M J hM hJM.le]
  exact beta_survival_pos K n ((J : ℝ)/M) (by positivity)
    ((div_lt_one (by exact_mod_cast hM : (0 : ℝ) < M)).mpr (by exact_mod_cast hJM))

/-- Actual conditioning of the beta grid on its retained bins. -/
def gridTailLaw (K n M J : ℕ) (hM : 0 < M) (hJM : J < M) : FiniteDist (Fin M) :=
  (gridLaw K n M hM).condition (fun j => J ≤ j.val) (gridLaw_tail_positive K n M J hM hJM)

theorem gridTailLaw_expectation (K n M J : ℕ) (hM : 0 < M) (hJM : J < M) (f : ℕ → ℝ) :
    (∑ j : Fin M,(gridTailLaw K n M J hM hJM).weight j*f j.val)=
      (∑ j ∈ Finset.Ico J M,((gridCDF K n M (j+1)-gridCDF K n M j : ℚ) : ℝ)*f j)/
        (∫ x : ℝ in (J : ℝ)/M..1,density K n x) := by
  unfold gridTailLaw FiniteDist.condition
  simp only [div_mul_eq_mul_div,ite_mul,zero_mul]
  rw [← Finset.sum_div,gridLaw_tail_mass K n M J hM hJM.le]
  congr 1
  simpa only [gridLaw] using sum_fin_tail M J (fun j => ((gridCDF K n M (j+1)-gridCDF K n M j : ℚ) : ℝ)*f j)

/-- The comparison remains a full eventwise bound after normalization by
the actual retained beta mass. -/
theorem gridTailLaw_quadrature (K n M J : ℕ) (hM : 0 < M) (hJM : J < M)
    (value : ℕ → ℝ) (integrand : ℝ → ℝ) (hcont : Continuous integrand)
    (error : ℝ)
    (hpoint : ∀ j ∈ Finset.Ico J M,∀ x ∈ Set.Icc ((j : ℝ)/M) ((j+1 : ℕ)/M),
      |density K n x*value j-integrand x| ≤ error*density K n x) :
    |(∑ j : Fin M,(gridTailLaw K n M J hM hJM).weight j*value j.val)-
      (∫ x : ℝ in (J : ℝ)/M..1,integrand x)/(∫ x : ℝ in (J : ℝ)/M..1,density K n x)| ≤ error := by
  have hp := beta_survival_pos K n ((J : ℝ)/M) (by positivity)
    ((div_lt_one (by exact_mod_cast hM : (0 : ℝ) < M)).mpr (by exact_mod_cast hJM))
  rw [gridTailLaw_expectation,← sub_div,abs_div,abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (scalar_grid_error K n M J hM hJM.le value integrand hcont error hpoint)

end
end AFT.BetaReference

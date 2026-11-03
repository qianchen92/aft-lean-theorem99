import AFT.BetaGridLaw

/-! # Dimension-free quadrature for the genuine beta density -/
namespace AFT.BetaReference
open MeasureTheory
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Scalar test quadrature on the retained beta bins.  The error is weighted
by their actual total probability, rather than by their number. -/
theorem scalar_grid_error (K n M J : ℕ) (hM : 0 < M) (hJM : J ≤ M)
    (value : ℕ → ℝ) (integrand : ℝ → ℝ) (hcont : Continuous integrand)
    (error : ℝ)
    (hpoint : ∀ j ∈ Finset.Ico J M, ∀ x ∈ Set.Icc ((j : ℝ)/M) ((j+1 : ℕ)/M),
      |density K n x*value j-integrand x| ≤ error*density K n x) :
    |(∑ j ∈ Finset.Ico J M,
      ((gridCDF K n M (j+1)-gridCDF K n M j : ℚ) : ℝ)*value j)-
      ∫ x : ℝ in (J : ℝ)/M..1,integrand x| ≤
        error*(∫ x : ℝ in (J : ℝ)/M..1,density K n x) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hd : Continuous (density K n) := by unfold density; fun_prop
  have hsum (f : ℝ → ℝ) (hf : Continuous f) :
      (∑ j ∈ Finset.Ico J M,∫ x : ℝ in (j : ℝ)/M..(j+1 : ℕ)/M,f x)=
        ∫ x : ℝ in (J : ℝ)/M..1,f x := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ:=volume)
      (a:=fun j : ℕ => (j : ℝ)/M) hJM (fun j _ => hf.intervalIntegrable ((j : ℝ)/M) ((j+1 : ℕ)/M))
    simpa only [div_self hMp.ne'] using hh
  have hatom (j : ℕ) (hj : j ∈ Finset.Ico J M) :
      ((gridCDF K n M (j+1)-gridCDF K n M j : ℚ) : ℝ)=
        ∫ x : ℝ in (j : ℝ)/M..(j+1 : ℕ)/M,density K n x :=
    gridLaw_weight_integral K n M hM ⟨j,(Finset.mem_Ico.mp hj).2⟩
  have hlocal (j : ℕ) (hj : j ∈ Finset.Ico J M) :
      |((gridCDF K n M (j+1)-gridCDF K n M j : ℚ) : ℝ)*value j-
        ∫ x : ℝ in (j : ℝ)/M..(j+1 : ℕ)/M,integrand x| ≤
        error*(∫ x : ℝ in (j : ℝ)/M..(j+1 : ℕ)/M,density K n x) := by
    have hab : (j : ℝ)/M ≤ (j+1 : ℕ)/M := div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hMp.le
    have hi : IntervalIntegrable (fun x => density K n x*value j) volume ((j : ℝ)/M) ((j+1 : ℕ)/M) :=
      (hd.mul continuous_const).intervalIntegrable _ _
    rw [hatom j hj,← intervalIntegral.integral_mul_const,← intervalIntegral.integral_sub hi (hcont.intervalIntegrable _ _)]
    apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hab
      (((hd.mul continuous_const).sub hcont).abs.intervalIntegrable _ _)
      ((continuous_const.mul hd).intervalIntegrable _ _) (hpoint j hj)
    simpa only [Pi.mul_apply,intervalIntegral.integral_const_mul] using hh
  rw [← hsum integrand hcont,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum hlocal).trans_eq
  rw [← Finset.mul_sum,hsum (density K n) hd]

end
end AFT.BetaReference

import AFT.BetaRationalCDF

/-! # The genuine beta law rounded upward to a finite rational grid -/
namespace AFT.BetaReference
open MeasureTheory
open scoped BigOperators

/-- Cumulative mass at the exact rational grid endpoint. -/
def gridCDF (K n M j : ℕ) : ℚ := rationalCDF K n ((j : ℚ)/M)

theorem gridCDF_zero (K n M : ℕ) : gridCDF K n M 0=0 := by simp [gridCDF]
theorem gridCDF_total (K n M : ℕ) (hM : 0<M) : gridCDF K n M M=1 := by
  simp [gridCDF,ne_of_gt hM]

theorem gridCDF_mono (K n M : ℕ) (hM : 0<M) : MonotoneOn (gridCDF K n M) (Set.Icc 0 M) := by
  intro i hi j hj hij
  apply rationalCDF_mono
  · positivity
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  · exact (div_le_one (by exact_mod_cast hM : (0 : ℚ)<M)).mpr (by exact_mod_cast hj.2)

noncomputable section

/-- Finite masses of the actual beta intervals. This is rounded continuous
beta, prior to the additional finite-random-bit CDF quantization. -/
def gridLaw (K n M : ℕ) (hM : 0<M) : FiniteDist (Fin M) where
  weight j := (gridCDF K n M (j.val+1)-gridCDF K n M j.val : ℚ)
  nonneg j := by
    exact_mod_cast sub_nonneg.mpr (gridCDF_mono K n M hM ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega))
  sum_one := by
    simp only [Rat.cast_sub]
    change (∑ j : Fin M, (((gridCDF K n M (j.val+1) : ℚ) : ℝ)-((gridCDF K n M j.val : ℚ) : ℝ)))=1
    rw [Fin.sum_univ_eq_sum_range (fun j => (gridCDF K n M (j+1) : ℝ)-(gridCDF K n M j : ℝ)),Finset.sum_range_sub (fun j => (gridCDF K n M j : ℝ)) M]
    simp only [gridCDF_zero,gridCDF_total K n M hM,Rat.cast_one,Rat.cast_zero,sub_zero]

/-- The sampled grid value is the upper endpoint of its bin. -/
def gridPoint (M : ℕ) (j : Fin M) : ℚ := (j.val+1 : ℕ)/M

theorem gridLaw_weight_integral (K n M : ℕ) (hM : 0<M) (j : Fin M) :
    (gridLaw K n M hM).weight j=∫ x : ℝ in (j.val : ℝ)/M..(j.val+1 : ℕ)/M,density K n x := by
  change ((gridCDF K n M (j.val+1)-gridCDF K n M j.val : ℚ) : ℝ)=_
  simp only [Rat.cast_sub,gridCDF,rationalCDF_eq_integral,Rat.cast_div,Rat.cast_natCast]
  have hi : Continuous (density K n) := by unfold density; fun_prop
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hi.intervalIntegrable 0 ((j.val : ℝ)/M))
    (hi.intervalIntegrable ((j.val : ℝ)/M) ((j.val+1 : ℕ)/M))
  linarith

/-- Every bin mass is at most `N/M`; this also controls the loss when a
continuous legality cutoff is rounded upward to the grid. -/
theorem gridLaw_weight_le (K n M : ℕ) (hM : 0<M) (j : Fin M) :
    (gridLaw K n M hM).weight j≤(K+n+1 : ℕ)/M := by
  rw [gridLaw_weight_integral]
  have hMp : (0 : ℝ)<M := by exact_mod_cast hM
  have hab : (j.val : ℝ)/M≤(j.val+1 : ℕ)/M := div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j.val) hMp.le
  have hi : Continuous (density K n) := by unfold density; fun_prop
  have hh := intervalIntegral.integral_mono_on (μ:=volume) hab (hi.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (g:=fun _ : ℝ => ((K+n+1 : ℕ) : ℝ)) (fun x hx => by
      simpa only [Nat.cast_add,Nat.cast_one] using density_le_population K n x
        ((div_nonneg (by positivity : (0 : ℝ)≤j.val) hMp.le).trans hx.1)
        (hx.2.trans ((div_le_one hMp).mpr (by exact_mod_cast j.isLt))))
  apply hh.trans_eq
  simp only [intervalIntegral.integral_const,smul_eq_mul]
  push_cast
  field_simp
  ring

end
end AFT.BetaReference

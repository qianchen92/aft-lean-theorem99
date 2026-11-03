import AFT.RationalLinearIteration

/-! # Entrywise numerical errors control the actual primary activity -/
namespace AFT
open scoped BigOperators
noncomputable section

theorem matrix_primaryActivity_le {Color : Type*} [Fintype Color]
    (matrix : Color → Color → ℝ) (profile primary : Color → ℝ) (rate lower error : ℝ)
    (hrate : 0≤rate) (hlower : 0<lower) (hp : ∀ color,lower≤primary color)
    (hmass : ∑ color,primary color=1) (he : 0≤error)
    (hentry : ∀ output input,|matrix output input|≤error) :
    primaryActivity rate primary (fun output => ∑ input,matrix output input*profile input)≤
      (error/lower*(1+rate))*primaryActivity rate primary profile := by
  have hpositive : ∀ color,0<primary color := fun color => hlower.trans_le (hp color)
  let output := fun color => ∑ input,matrix color input*profile input
  let bound := error/lower
  have hb : 0≤bound := div_nonneg he hlower.le
  have hrow (color : Color) : |output color|≤error*Real.sqrt (profileSquareNorm primary profile) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ input,error*|profile input| := by
        apply Finset.sum_le_sum
        intro input _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hentry color input) (abs_nonneg _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (profile_l1_le_sqrt primary profile hpositive hmass) he
  have hdensity (color : Color) : |output color/primary color|≤
      bound*Real.sqrt (profileSquareNorm primary profile) := by
    rw [abs_div,abs_of_pos (hpositive color)]
    calc
      _ ≤ error*Real.sqrt (profileSquareNorm primary profile)/primary color :=
        div_le_div_of_nonneg_right (hrow color) (hpositive color).le
      _ ≤ error*Real.sqrt (profileSquareNorm primary profile)/lower :=
        div_le_div_of_nonneg_left (mul_nonneg he (Real.sqrt_nonneg _)) hlower (hp color)
      _ = _ := by dsimp only [bound];ring
  have hh : Real.sqrt (profileSquareNorm primary output)≤bound*Real.sqrt (profileSquareNorm primary profile) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hb (Real.sqrt_nonneg _),?_⟩
    rw [← densityScore_square]
    unfold densitySquareNorm
    calc
      _ ≤ ∑ color,primary color*(bound*Real.sqrt (profileSquareNorm primary profile))^2 := by
        apply Finset.sum_le_sum
        intro color _
        apply mul_le_mul_of_nonneg_left _ (hpositive color).le
        have hsq := pow_le_pow_left₀ (abs_nonneg _) (hdensity color) 2
        simpa only [sq_abs] using hsq
      _ = _ := by rw [← Finset.sum_mul,hmass,one_mul]
  have hinf : ‖fun color => output color/primary color‖≤bound*Real.sqrt (profileSquareNorm primary profile) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (Real.sqrt_nonneg _))).mpr
    intro color
    simpa only [Real.norm_eq_abs] using hdensity color
  have hmain := primaryActivity_bound_of_parts rate primary profile output bound bound hrate
    (add_nonneg hb (mul_nonneg hrate hb)) hh hinf
  apply hmain.trans_eq
  congr 1
  dsimp only [bound]
  ring

theorem rationalMatrix_difference_primaryActivity {Color : Type*} [Fintype Color]
    (approximate : Color → Color → ℚ) (actual : Color → Color → ℝ)
    (profile primary : Color → ℝ) (rate lower error : ℝ)
    (hrate : 0≤rate) (hlower : 0<lower) (hp : ∀ color,lower≤primary color)
    (hmass : ∑ color,primary color=1) (he : 0≤error)
    (hentry : ∀ output input,|(approximate output input : ℝ)-actual output input|≤error) :
    primaryActivity rate primary
      (RationalNumerics.realMatrixOperator approximate profile-
        (fun output => ∑ input,actual output input*profile input))≤
      (error/lower*(1+rate))*primaryActivity rate primary profile := by
  convert matrix_primaryActivity_le (fun output input => (approximate output input : ℝ)-actual output input)
    profile primary rate lower error hrate hlower hp hmass he hentry using 1
  congr 1
  funext output
  simp only [RationalNumerics.realMatrixOperator,LinearMap.coe_mk,AddHom.coe_mk,Pi.sub_apply,
    sub_mul,Finset.sum_sub_distrib]

end
end AFT

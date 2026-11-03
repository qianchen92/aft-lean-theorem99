import AFT.BackgroundBoundaryTransform
import AFT.JointBoundaryAlgebra

/-! # Exact polynomial evaluation of complete joint profile transforms -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color] [DecidableEq Color]

def jointDensityForm (reference : Slot → FiniteDist Color) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] Table Color where
  toFun kernel := ∑ word, MvPolynomial.C (kernel word*∏ slot,(reference slot).weight (word slot))*
    ∏ slot,MvPolynomial.X (word slot)
  map_add' first second := by
    simp only [Pi.add_apply,add_mul,map_add,Finset.sum_add_distrib]
  map_smul' scalar kernel := by
    simp only [Pi.smul_apply,smul_eq_mul,MvPolynomial.smul_eq_C_mul,map_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro word _
    ring

omit [DecidableEq Color] in
theorem jointDensityForm_apply (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ) :
    jointDensityForm reference kernel =
      ∑ word,MvPolynomial.C (kernel word*∏ slot,(reference slot).weight (word slot))*
        ∏ slot,MvPolynomial.X (word slot) := rfl

theorem profilePolynomialMap_X (operator : Module.End ℝ (Color → ℝ)) (color : Color) :
    profilePolynomialMap operator (MvPolynomial.X color)=
      ∑ output,MvPolynomial.C (LinearMap.toMatrix' operator output color)*MvPolynomial.X output := by
  rw [profilePolynomialMap,MvPolynomial.aeval_X,profileForm_apply]
  simp only [LinearMap.toMatrix'_apply]

theorem profilePolynomialMap_jointDensityForm (operator : Module.End ℝ (Color → ℝ))
    (reference : Slot → FiniteDist Color) (coordinates : List Slot)
    (hnodup : coordinates.Nodup) (hcomplete : ∀ slot,slot∈coordinates)
    (hpositive : ∀ slot color,(reference slot).weight color≠0)
    (kernel : (Slot → Color) → ℝ) :
    profilePolynomialMap operator (jointDensityForm reference kernel)=
      jointDensityForm reference (MixedKernel.inputIteration coordinates (fun _ => operator) reference kernel) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Color) (Classical.decEq Color)
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  rw [jointDensityForm_apply]
  simp only [map_sum,map_mul,map_prod,profilePolynomialMap_X]
  have he (value : ℝ) : profilePolynomialMap operator (MvPolynomial.C value)=MvPolynomial.C value :=
    (profilePolynomialMap operator).commutes value
  simp_rw [he,Fintype.prod_sum,Finset.prod_mul_distrib,← map_prod,Finset.mul_sum]
  rw [Finset.sum_comm,jointDensityForm_apply]
  apply Finset.sum_congr rfl
  intro output _
  rw [mul_comm (MixedKernel.inputIteration coordinates (fun _ => operator) reference kernel output),
    MixedKernel.weighted_inputIteration_matrix coordinates hnodup hcomplete _ _ hpositive]
  simp only [map_sum,Finset.sum_mul,map_mul]
  apply Finset.sum_congr rfl
  intro point _
  ring

omit [DecidableEq Color] in
theorem jointDensityForm_smul (reference : Slot → FiniteDist Color)
    (scalar : ℝ) (kernel : (Slot → Color) → ℝ) :
    jointDensityForm reference (scalar • kernel)=MvPolynomial.C scalar*jointDensityForm reference kernel := by
  rw [map_smul,MvPolynomial.smul_eq_C_mul]

/-- Composition with a polynomial profile transform preserves the input
order filtration, so the exact identities also hold in every cutoff ring. -/
theorem profilePolynomialMap_hasOrder (operator : Module.End ℝ (Color → ℝ))
    (minimum : ℕ) (table : Table Color) (h : HasOrder (fun _ => 1) minimum table) :
    HasOrder (fun _ => 1) minimum (profilePolynomialMap operator table) := by
  apply aeval_hasOrder (fun _ => 1) _ _ minimum table h
  intro color
  rw [profileForm_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro output _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem profilePolynomialMap_truncation_respects (operator : Module.End ℝ (Color → ℝ))
    (cutoff : ℕ) (first second : Table Color)
    (h : truncate (fun _ => 1) cutoff first=truncate (fun _ => 1) cutoff second) :
    truncate (fun _ => 1) cutoff (profilePolynomialMap operator first)=
      truncate (fun _ => 1) cutoff (profilePolynomialMap operator second) := by
  have hh : HasOrder (fun _ => 1) (cutoff+1) (first-second) := by
    intro powers hp
    have hc := congrArg (MvPolynomial.coeff powers) h
    simp only [coeff_truncate,if_pos (show weightedOrder (fun _ => 1) powers≤cutoff by omega)] at hc
    simp only [MvPolynomial.coeff_sub,hc,sub_self]
  have hm := profilePolynomialMap_hasOrder operator (cutoff+1) (first-second) hh
  have hz := truncate_of_hasOrder (fun _ => 1) cutoff _ hm
  rw [map_sub,truncate_sub] at hz
  exact sub_eq_zero.mp hz

end
end AFT.RepresentedPolynomial

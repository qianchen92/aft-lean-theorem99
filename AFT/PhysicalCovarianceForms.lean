import AFT.CovarianceOutput
import AFT.CenteredPolynomial
import AFT.PhysicalBlockTensors

/-! # Actual covariance tables equal the complete physical centered generating law -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

theorem pairForm_word (mass : Color → Color → ℝ) :
    (∑ word : Fin 2 → Color, MvPolynomial.C (mass (word 0) (word 1)) * ∏ slot, MvPolynomial.X (word slot)) = pairForm mass := by
  rw [← (finTwoArrowEquiv Color).symm.sum_comp, Fintype.sum_prod_type]
  unfold pairForm
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [Fin.prod_univ_two, finTwoArrowEquiv, Equiv.coe_fn_symm_mk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem jointPrimaryForm_pair (primary : FiniteDist Color) (kernel : Color → Color → ℝ) :
    jointPrimaryForm primary (primaryPairInput kernel) =
      pairForm (fun first second => kernel first second * (primary.weight first * primary.weight second)) := by
  unfold jointPrimaryForm
  change (∑ word : Fin 2 → Color, MvPolynomial.C (kernel (word 0) (word 1) * ∏ slot, primary.weight (word slot)) * ∏ slot, MvPolynomial.X (word slot)) = _
  rw [← (finTwoArrowEquiv Color).symm.sum_comp, Fintype.sum_prod_type]
  unfold pairForm
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [Fin.prod_univ_two, finTwoArrowEquiv, Equiv.coe_fn_symm_mk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem jointPrimaryForm_triple (primary : FiniteDist Color) (kernel : (Fin 3 → Color) → ℝ) :
    jointPrimaryForm primary (primaryTripleInput kernel) =
      tripleForm (fun first second third => kernel ![first, second, third] *
        (primary.weight first * primary.weight second * primary.weight third)) := by
  unfold jointPrimaryForm
  change (∑ word : Fin 3 → Color, MvPolynomial.C (kernel word * ∏ slot, primary.weight (word slot)) * ∏ slot, MvPolynomial.X (word slot)) = _
  rw [← PhysicalBlockTensors.tripleEquiv.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  unfold tripleForm
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  simp only [Fin.prod_univ_three, PhysicalBlockTensors.tripleEquiv, Equiv.coe_fn_symm_mk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

def covariancePairFormLinear : (Color → Color → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun := pairForm
  map_add' := pairForm_add
  map_smul' := by intro scalar mass; simpa only [MvPolynomial.smul_eq_C_mul] using pairForm_smul scalar mass

def covarianceTripleFormLinear : (Color → Color → Color → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun := tripleForm
  map_add' := by intro first second; simp [tripleForm, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar mass
    simp only [tripleForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
      RingHom.id_apply, MvPolynomial.smul_eq_C_mul, mul_assoc]

def covarianceTripleGeneratingLinear (reference : Color → ℝ) :
    (Color → Color → Color → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun := tripleGenerating reference
  map_add' := by intro first second; simp [tripleGenerating, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar mass
    simp only [tripleGenerating, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
      RingHom.id_apply, MvPolynomial.smul_eq_C_mul, mul_assoc]

/-- A finite source average retains all three covariance contributions. -/
theorem tripleGenerating_source_covariance {Source : Type*} [Fintype Source]
    (reference : Color → ℝ) (weight : Source → ℝ)
    (pair : Source → Color → Color → ℝ) (single : Source → Color → ℝ)
    (hp : ∀ source, (∑ a, ∑ b, pair source a b) = 0)
    (hs : ∀ source, (∑ c, single source c) = 0) :
    tripleGenerating reference (fun a b c => ∑ source, weight source * pair source a b * single source c) =
      tripleForm (fun a b c => ∑ source, weight source * SafePair.canonicalPair reference (pair source) a b * single source c) +
      pairForm (fun a c => ∑ source, weight source * (∑ b, pair source a b) * single source c) +
      pairForm (fun b c => ∑ source, weight source * (∑ a, pair source a b) * single source c) := by
  have he (pair : Source → Color → Color → ℝ) :
      (fun a b c => ∑ source, weight source * pair source a b * single source c) =
      ∑ source, weight source • (fun a b c => pair source a b * single source c) := by
    ext a b c
    simp [Finset.sum_apply, mul_assoc]
  have he2 (row : Source → Color → ℝ) :
      (fun a c => ∑ source, weight source * row source a * single source c) =
      ∑ source, weight source • (fun a c => row source a * single source c) := by
    ext a c
    simp [Finset.sum_apply, mul_assoc]
  change covarianceTripleGeneratingLinear reference _ = covarianceTripleFormLinear _ + covariancePairFormLinear _ + covariancePairFormLinear _
  rw [he pair, he (fun source => SafePair.canonicalPair reference (pair source)), he2, he2,
    map_sum, map_sum, map_sum, map_sum]
  simp only [map_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _
  change weight source • tripleGenerating reference _ = _
  rw [tripleGenerating_covariance reference (pair source) (single source) (hp source) (hs source), smul_add, smul_add]
  rfl

end
end AFT.RepresentedPolynomial

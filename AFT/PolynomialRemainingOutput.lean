import AFT.PolynomialCoordinateOutput

/-! # Polynomial-valued contractions of unchanged original coordinates -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Rest Color Output : Type*} [Fintype Rest] [DecidableEq Rest] [Fintype Color]

def polynomialRemainingOutput (reference : Rest → FiniteDist Color)
    (forms : Rest → Color → Table Output) :
    ((Rest → Color) → Table Output) →ₗ[ℝ] Table Output where
  toFun value := ∑ rest,MvPolynomial.C (∏ slot,(reference slot).weight (rest slot))*value rest*
    ∏ slot,forms slot (rest slot)
  map_add' first second := by
    simp only [Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' scalar value := by
    simp only [Pi.smul_apply,Algebra.smul_def,MvPolynomial.algebraMap_eq,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rest _
    ring

end
end AFT.RepresentedPolynomial

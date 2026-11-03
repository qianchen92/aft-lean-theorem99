import AFT.DependentOldCentering
import AFT.MixedCoordinateProducts

/-! # A finite canonical point basis, including reference laws with zeros -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- Centered point indicators have no probability denominator.  They are
therefore valid also on the zero atoms of the safe body-center law. -/
def canonicalPointBasis (reference : Slot → FiniteDist Color) (point word : Slot → Color) : ℝ :=
  ∏ slot,((if word slot=point slot then 1 else 0)-(reference slot).weight (point slot))

theorem canonicalPointBasis_canonical (reference : Slot → FiniteDist Color) (point : Slot → Color) :
    Hoeffding.Canonical reference Finset.univ (canonicalPointBasis reference point) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  constructor
  · intro first second h
    have hh : first=second := funext fun slot => h slot (Finset.mem_univ slot)
    rw [hh]
  · intro fixed _ word
    change (∑ color,(reference fixed).weight color*
      canonicalPointBasis reference point (Function.update word fixed color))=0
    have hprod (color : Color) : canonicalPointBasis reference point (Function.update word fixed color)=
        ((if color=point fixed then 1 else 0)-(reference fixed).weight (point fixed))*
          ∏ slot∈Finset.univ.erase fixed,
            ((if word slot=point slot then 1 else 0)-(reference slot).weight (point slot)) := by
      unfold canonicalPointBasis
      rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ fixed),Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro slot hs
      rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
    simp only [hprod,←mul_assoc,←Finset.sum_mul]
    have hzero : (∑ color,(reference fixed).weight color*
        ((if color=point fixed then 1 else 0)-(reference fixed).weight (point fixed)))=0 := by
      simp only [mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero,
        Finset.sum_ite_eq',Finset.mem_univ,if_true,←Finset.sum_mul,FiniteDist.sum_one,one_mul,sub_self]
    rw [hzero,zero_mul]

/-- Every canonical joint kernel is a linear combination of these actual
canonical basis kernels, with its original point values as coefficients. -/
theorem canonicalPointBasis_expansion (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hc : Hoeffding.Canonical reference Finset.univ kernel)
    (word : Slot → Color) :
    (∑ point,kernel point*canonicalPointBasis reference point word)=kernel word := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have hh := RepresentedPolynomial.dependentPolynomial_sub_weighted_constants (Output:=Unit)
    reference (fun slot color => MvPolynomial.C (R:=ℝ) (if word slot=color then 1 else 0))
    (fun _ => 1) kernel Finset.univ (by
      intro slot _ tail
      exact RepresentedPolynomial.dependent_centered_tail_of_update reference kernel slot
        (hc.2 slot (Finset.mem_univ slot)) tail)
  simp only [Finset.mem_univ,if_true,mul_one,RepresentedPolynomial.dependentPolynomial,
    ←map_sub,←map_prod,←map_mul,←map_sum] at hh
  have he := MvPolynomial.C_injective Unit ℝ hh
  have hx := congrFun (kernel_product_expansion kernel) word
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,productKernel] at hx
  exact he.trans hx.symm

end
end AFT.MixedKernel

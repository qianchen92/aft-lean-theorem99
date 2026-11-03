import CurrentAFT.LeadingEvaluation

/-! # The actual truncated endpoint evaluation of canonical kernel families -/

namespace CurrentAFT.LeadingEvaluation

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

local instance familyFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]

def homogeneousLinear (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order r s : ℕ) :
    canonicalKernels primary body r s →ₗ[ℝ] TruncatedOutput.Polynomial Variable order :=
  (TruncatedOutput.quotientMap order).toLinearMap.comp
    ((kernelLinear primary body primaryForm bodyForm).comp
      (Submodule.subtype (canonicalKernels primary body r s)))

def familyLinear (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ) :
    KernelFamily primary body order →ₗ[ℝ] TruncatedOutput.Polynomial Variable order :=
  ∑ arity : TruncatedArity order,
    (homogeneousLinear primary body primaryForm bodyForm order arity.val.1.val arity.val.2.val).comp
      (LinearMap.proj arity)

theorem familyLinear_apply (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ)
    (family : KernelFamily primary body order) :
    familyLinear primary body primaryForm bodyForm order family =
      ∑ arity : TruncatedArity order,
        TruncatedOutput.quotientMap order
          (kernelPolynomial primary body primaryForm bodyForm (family arity).val) := by
  simp only [familyLinear, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, homogeneousLinear, Submodule.subtype_apply]
  rfl

theorem familyLinear_single (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ)
    (arity : TruncatedArity order)
    (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val) :
    familyLinear primary body primaryForm bodyForm order (Pi.single arity kernel) =
      homogeneousLinear primary body primaryForm bodyForm order _ _ kernel := by
  simp only [familyLinear, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  change (∑ other : TruncatedArity order,
    homogeneousLinear primary body primaryForm bodyForm order other.val.1.val other.val.2.val
      ((Pi.single arity kernel : KernelFamily primary body order) other)) = _
  rw [Finset.sum_eq_single arity]
  · rw [Pi.single_eq_same]
  · intro other _ hother
    rw [Pi.single_eq_of_ne (M := fun index : TruncatedArity order =>
      canonicalKernels primary body index.val.1.val index.val.2.val) hother, map_zero]
  · simp

theorem kernelPolynomial_scalar (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (scalar : ℝ) :
    kernelPolynomial primary body primaryForm bodyForm (scalarKernel primary body scalar).val =
      MvPolynomial.C scalar := by
  simp [kernelPolynomial, scalarKernel]

theorem familyLinear_one (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ) :
    familyLinear primary body primaryForm bodyForm order 1 = 1 := by
  have hunit : scalarUnit primary body = scalarKernel primary body 1 := by
    apply Subtype.ext
    rfl
  change familyLinear primary body primaryForm bodyForm order
    (Pi.single (zeroArity order) (scalarUnit primary body)) = _
  rw [hunit]
  rw [familyLinear_single]
  change TruncatedOutput.quotientMap order
    (kernelPolynomial primary body primaryForm bodyForm (scalarKernel primary body 1).val) = _
  rw [kernelPolynomial_scalar, map_one, map_one]

theorem homogeneousLinear_product (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    homogeneousLinear primary body primaryForm bodyForm order (r + r') (s + s')
      (homogeneousProduct primary body first second) =
      homogeneousLinear primary body primaryForm bodyForm order r s first *
        homogeneousLinear primary body primaryForm bodyForm order r' s' second := by
  change TruncatedOutput.quotientMap order
    (kernelPolynomial primary body primaryForm bodyForm (homogeneousProduct primary body first second).val) = _
  rw [kernelPolynomial_homogeneousProduct, map_mul]
  rfl

theorem homogeneousLinear_above (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1)
    (order r s : ℕ) (habove : order < r + s)
    (kernel : canonicalKernels primary body r s) :
    homogeneousLinear primary body primaryForm bodyForm order r s kernel = 0 := by
  apply Subtype.ext
  change AFT.RepresentedPolynomial.truncate (fun _ : Variable => 1) order
    (kernelPolynomial primary body primaryForm bodyForm kernel.val) = 0
  have hhomogeneous := kernelPolynomial_homogeneous primary body primaryForm bodyForm
    hprimary hbody kernel.val
  simp only [Fintype.card_fin] at hhomogeneous
  ext powers
  rw [AFT.RepresentedPolynomial.coeff_truncate, MvPolynomial.coeff_zero]
  split_ifs with hdegree
  · apply hhomogeneous.coeff_eq_zero
    have hne : AFT.RepresentedPolynomial.weightedOrder (fun _ : Variable => 1) powers ≠ r + s := by omega
    simpa only [AFT.RepresentedPolynomial.weightedOrder, mul_one] using hne
  · rfl

theorem familyLinear_single_product (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1) (order : ℕ)
    (left right : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val) :
    familyLinear primary body primaryForm bodyForm order
      ((Pi.single left first : KernelFamily primary body order) * Pi.single right second) =
      familyLinear primary body primaryForm bodyForm order (Pi.single left first) *
        familyLinear primary body primaryForm bodyForm order (Pi.single right second) := by
  rw [familyLinear_single, familyLinear_single]
  change familyLinear primary body primaryForm bodyForm order
    (familyProduct primary body order (Pi.single left first) (Pi.single right second)) = _
  by_cases hdegree : (left.val.1.val + right.val.1.val) +
      (left.val.2.val + right.val.2.val) ≤ order
  · rw [familyProduct_single_retained primary body order left right first second hdegree,
      familyLinear_single]
    exact homogeneousLinear_product primary body primaryForm bodyForm order first second
  · rw [familyProduct_single_dropped primary body order left right first second (by omega), map_zero]
    rw [← homogeneousLinear_product]
    exact (homogeneousLinear_above primary body primaryForm bodyForm hprimary hbody order _ _
      (by omega) (homogeneousProduct primary body first second)).symm

theorem familyLinear_product (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1) (order : ℕ)
    (first second : KernelFamily primary body order) :
    familyLinear primary body primaryForm bodyForm order (first * second) =
      familyLinear primary body primaryForm bodyForm order first *
        familyLinear primary body primaryForm bodyForm order second := by
  let evaluation := familyLinear primary body primaryForm bodyForm order
  have hfirst : first = ∑ arity, Pi.single arity (first arity) :=
    (Finset.univ_sum_single first).symm
  have hsecond : second = ∑ arity, Pi.single arity (second arity) :=
    (Finset.univ_sum_single second).symm
  change evaluation (first * second) = evaluation first * evaluation second
  conv_lhs => rw [hfirst, hsecond]
  conv_rhs => rw [hfirst, hsecond]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  exact familyLinear_single_product primary body primaryForm bodyForm hprimary hbody order
    right left (first right) (second left)

instance familyRealAlgebra (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    Algebra ℝ (KernelFamily primary body order) :=
  Algebra.ofModule (CommonQueueAssembly.family_smul_mul primary body order)
    (CommonQueueAssembly.family_mul_smul primary body order)

/-- Evaluation is an algebra homomorphism because it evaluates the actual
disjoint tensors and kills precisely the terms beyond the stated cutoff. -/
def familyHom (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1) (order : ℕ) :
    KernelFamily primary body order →ₐ[ℝ] TruncatedOutput.Polynomial Variable order where
  toFun := familyLinear primary body primaryForm bodyForm order
  map_zero' := map_zero _
  map_one' := familyLinear_one primary body primaryForm bodyForm order
  map_add' := map_add _
  map_mul' := familyLinear_product primary body primaryForm bodyForm hprimary hbody order
  commutes' scalar := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, familyLinear_one,
      Algebra.algebraMap_eq_smul_one]

end

end CurrentAFT.LeadingEvaluation

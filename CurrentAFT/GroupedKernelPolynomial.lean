import CurrentAFT.GroupedKernelProductFinite
import CurrentAFT.GroupedKernelLinear
import CurrentAFT.LeadingEvaluation

/-! # Exact physical polynomial image of the joint grouped tensor -/
namespace CurrentAFT.GroupedKernelPolynomial
open AFT ControlCoordinates ControlProduct GradedControlAlgebra LeadingEvaluation
  GroupedKernelNorm GroupedKernelProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
  (primary : FiniteDist Primary) (body : FiniteDist Body)
  (primaryForm : Primary → MvPolynomial Variable ℝ) (bodyForm : Body → MvPolynomial Variable ℝ)

theorem iteratedProduct_polynomial (count : ℕ) (r s : Fin count → ℕ)
    (kernels : (index : Fin count) → canonicalKernels primary body (r index) (s index)) :
    kernelPolynomial primary body primaryForm bodyForm (iteratedProduct primary body count r s kernels).val =
      ∏ index, kernelPolynomial primary body primaryForm bodyForm (kernels index).val := by
  induction count with
  | zero =>
    change kernelPolynomial primary body primaryForm bodyForm
      (fun (_ : Fin 0 → Primary) (_ : Fin 0 → Body) => 1) = 1
    simp [kernelPolynomial]
  | succ count ih =>
    rw [iteratedProduct, transportKernel_val, kernelPolynomial_reindex,
      kernelPolynomial_homogeneousProduct, ih, Fin.prod_univ_succ]

variable {Group : Type*} [Fintype Group]

theorem finiteProduct_polynomial (r s : Group → ℕ)
    (kernels : (group : Group) → canonicalKernels primary body (r group) (s group)) :
    kernelPolynomial primary body primaryForm bodyForm (finiteProduct primary body r s kernels).val =
      ∏ group, kernelPolynomial primary body primaryForm bodyForm (kernels group).val := by
  rw [finiteProduct, transportKernel_val, kernelPolynomial_reindex, iteratedProduct_polynomial]
  exact Equiv.prod_comp (Fintype.equivFin Group).symm
    (fun group => kernelPolynomial primary body primaryForm bodyForm (kernels group).val)

theorem canonicalize_polynomial {PS BS : Group → Type*} [∀ group, Fintype (PS group)]
    [∀ group, Fintype (BS group)] {PT BT : Type*} [Fintype PT] [Fintype BT]
    (primaryEquiv : Sigma PS ≃ PT) (bodyEquiv : Sigma BS ≃ BT)
    (kernel : GroupWord (Primary := Primary) (Body := Body) PS BS → ℝ) :
    kernelPolynomial primary body primaryForm bodyForm (canonicalize PS BS primaryEquiv bodyEquiv kernel) =
      kernelPolynomial primary body primaryForm bodyForm (flatten PS BS kernel) := by
  rw [canonicalize, kernelPolynomial_symmetrize, kernelPolynomial_reindex]

theorem canonicalize_product_polynomial (r s : Group → ℕ)
    {PT BT : Type*} [Fintype PT] [Fintype BT]
    (primaryEquiv : Sigma (fun group => Fin (r group)) ≃ PT)
    (bodyEquiv : Sigma (fun group => Fin (s group)) ≃ BT)
    (kernels : (group : Group) → canonicalKernels primary body (r group) (s group)) :
    kernelPolynomial primary body primaryForm bodyForm
      (canonicalize (fun group => Fin (r group)) (fun group => Fin (s group)) primaryEquiv bodyEquiv
        (fun word => ∏ group, (kernels group).val (word group).1 (word group).2)) =
      ∏ group, kernelPolynomial primary body primaryForm bodyForm (kernels group).val := by
  rw [canonicalize_polynomial]
  have h := finiteProduct_polynomial primary body primaryForm bodyForm r s kernels
  rw [finiteProduct_val, canonicalize_polynomial] at h
  exact h

def fiberChannel {Source : Type*} {r s : ℕ}
    (channel : (Source → ℝ) →ₗ[ℝ] canonicalKernels primary body r s) :
    (Source → ℝ) →ₗ[ℝ] (((Fin r → Primary) × (Fin s → Body)) → ℝ) where
  toFun input output := (channel input).val output.1 output.2
  map_add' first second := by
    funext output
    exact congrArg (fun kernel : canonicalKernels primary body r s => kernel.val output.1 output.2)
      (channel.map_add first second)
  map_smul' scalar input := by
    funext output
    exact congrArg (fun kernel : canonicalKernels primary body r s => kernel.val output.1 output.2)
      (channel.map_smul scalar input)

variable {Input : Group → Type*} [∀ group, Fintype (Input group)]

/-- Polynomial evaluation commutes with the same joint tensor used for
the Hilbert bound. The complete joint source remains inside one sum. -/
theorem tensor_polynomial (r s : Group → ℕ)
    {PT BT : Type*} [Fintype PT] [Fintype BT]
    (primaryEquiv : Sigma (fun group => Fin (r group)) ≃ PT)
    (bodyEquiv : Sigma (fun group => Fin (s group)) ≃ BT)
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] canonicalKernels primary body (r group) (s group))
    (input : ((group : Group) → Input group) → ℝ) :
    kernelPolynomial primary body primaryForm bodyForm
      (canonicalize (fun group => Fin (r group)) (fun group => Fin (s group)) primaryEquiv bodyEquiv
        (DependentTensorChannel.apply (fun group => fiberChannel primary body (channels group)) input)) =
      ∑ source, input source • ∏ group,
        kernelPolynomial primary body primaryForm bodyForm (channels group (Pi.single (source group) 1)).val := by
  rw [canonicalize_tensor_formula]
  change kernelLinear primary body primaryForm bodyForm _ = _
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  exact canonicalize_product_polynomial primary body primaryForm bodyForm r s primaryEquiv bodyEquiv
    (fun group => channels group (Pi.single (source group) 1))

end
end CurrentAFT.GroupedKernelPolynomial

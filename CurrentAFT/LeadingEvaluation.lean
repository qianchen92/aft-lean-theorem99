import CurrentAFT.CommonQueueAssembly
import CurrentAFT.TruncatedOutput
import AFT.ReindexedCoefficients
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Literal endpoint evaluation of two-pool control kernels

The primary and body alphabets may differ. Every coefficient below is the
finite reference expectation of the actual joint kernel. Slot relabeling,
permutation averaging and disjoint-slot multiplication are proved identities
of these polynomials.
-/

namespace CurrentAFT.LeadingEvaluation

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) :=
  Classical.decEq _

variable {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]

def kernelPolynomial {PS BS : Type*} [Fintype PS] [Fintype BS]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : MvPolynomial Variable ℝ :=
  ∑ colors : PS → Primary, ∑ centers : BS → Body,
    MvPolynomial.C ((∏ index, primary.weight (colors index)) *
      (∏ index, body.weight (centers index)) * kernel colors centers) *
      ((∏ index, primaryForm (colors index)) * ∏ index, bodyForm (centers index))

def kernelLinear {PS BS : Type*} [Fintype PS] [Fintype BS]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) :
    Kernel (Primary := Primary) (Body := Body) PS BS →ₗ[ℝ] MvPolynomial Variable ℝ where
  toFun := kernelPolynomial primary body primaryForm bodyForm
  map_add' first second := by
    simp only [kernelPolynomial, Pi.add_apply, mul_add, map_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' scalar kernel := by
    simp only [kernelPolynomial, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Algebra.smul_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro colors _
    apply Finset.sum_congr rfl
    intro centers _
    simp only [map_mul, MvPolynomial.algebraMap_eq]
    ring

theorem kernelPolynomial_reindex {PS BS PT BT : Type*}
    [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    kernelPolynomial primary body primaryForm bodyForm
      (reindexKernel primaryEquiv bodyEquiv kernel) =
      kernelPolynomial primary body primaryForm bodyForm kernel := by
  unfold kernelPolynomial
  rw [← (HistogramNormalization.renameWord (Color := Primary) primaryEquiv).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro colors _
  rw [← (HistogramNormalization.renameWord (Color := Body) bodyEquiv).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro centers _
  have hp := primaryEquiv.prod_comp (fun index => primary.weight (colors index))
  have hb := bodyEquiv.prod_comp (fun index => body.weight (centers index))
  have hpf := primaryEquiv.prod_comp (fun index => primaryForm (colors index))
  have hbf := bodyEquiv.prod_comp (fun index => bodyForm (centers index))
  simp only [HistogramNormalization.renameWord, Equiv.coe_fn_symm_mk, reindexKernel,
    Function.comp_def] at *
  rw [hp, hb, hpf, hbf]

theorem kernelPolynomial_symmetrize {PS BS : Type*} [Fintype PS] [Fintype BS]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    kernelPolynomial primary body primaryForm bodyForm (symmetrize kernel) =
      kernelPolynomial primary body primaryForm bodyForm kernel := by
  change kernelLinear primary body primaryForm bodyForm (symmetrize kernel) = _
  simp only [ControlProduct.symmetrize, map_sum, map_smul]
  change (∑ primaryOrder : Equiv.Perm PS, (FiniteDist.uniform _).weight primaryOrder •
    ∑ bodyOrder : Equiv.Perm BS, (FiniteDist.uniform _).weight bodyOrder •
      kernelPolynomial primary body primaryForm bodyForm
        (reindexKernel primaryOrder bodyOrder kernel)) = _
  simp only [kernelPolynomial_reindex, ← Finset.sum_smul,
    (FiniteDist.uniform (Equiv.Perm BS)).sum_one,
    (FiniteDist.uniform (Equiv.Perm PS)).sum_one, one_smul]

theorem kernelPolynomial_disjointTensor {PS BS PT BT : Type*}
    [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    kernelPolynomial primary body primaryForm bodyForm (disjointTensor first second) =
      kernelPolynomial primary body primaryForm bodyForm first *
        kernelPolynomial primary body primaryForm bodyForm second := by
  unfold kernelPolynomial
  rw [← (Equiv.sumArrowEquivProdArrow PS PT Primary).symm.sum_comp,
    Fintype.sum_prod_type]
  conv_rhs =>
    rw [Finset.sum_mul]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro leftColors _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rightColors _
  rw [← (Equiv.sumArrowEquivProdArrow BS BT Body).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro leftCenters _
  apply Finset.sum_congr rfl
  intro rightCenters _
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, disjointTensor, Function.comp_def, map_mul]
  ring

theorem kernelPolynomial_homogeneousProduct
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    kernelPolynomial primary body primaryForm bodyForm
      (homogeneousProduct primary body first second).val =
      kernelPolynomial primary body primaryForm bodyForm first.val *
        kernelPolynomial primary body primaryForm bodyForm second.val := by
  change kernelPolynomial primary body primaryForm bodyForm
    (symmetrize (finDisjointTensor first.val second.val)) = _
  rw [kernelPolynomial_symmetrize]
  unfold finDisjointTensor
  rw [kernelPolynomial_reindex, kernelPolynomial_disjointTensor]

theorem kernelPolynomial_homogeneous {PS BS : Type*} [Fintype PS] [Fintype BS]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    (kernelPolynomial primary body primaryForm bodyForm kernel).IsHomogeneous
      (Fintype.card PS + Fintype.card BS) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro colors _
  apply MvPolynomial.IsHomogeneous.sum
  intro centers _
  apply MvPolynomial.IsHomogeneous.C_mul
  convert (MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun index : PS => primaryForm (colors index)) (fun _ => 1)
    (fun index _ => hprimary (colors index))).mul
    (MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun index : BS => bodyForm (centers index)) (fun _ => 1)
      (fun index _ => hbody (centers index))) using 1
  simp

end

end CurrentAFT.LeadingEvaluation

import CurrentAFT.CanonicalReconstruction
import CurrentAFT.FamilyEvaluation

/-! # Literal polynomial factors of the actual centered-point tensors -/

namespace CurrentAFT.PointPolynomial

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
  CanonicalReconstruction LeadingEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]

def atomForm {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (forms : Color → MvPolynomial Variable ℝ) (source : Color) : MvPolynomial Variable ℝ :=
  ∑ output, MvPolynomial.C (law.weight output * Hoeffding.centeredAtom law source output) * forms output

theorem pointTensor_polynomial (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ) (bodyForm : Body → MvPolynomial Variable ℝ)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    kernelPolynomial primary body primaryForm bodyForm (pointTensor primary body sourcePrimary sourceBody) =
      (∏ index, atomForm primary primaryForm (sourcePrimary index)) *
        ∏ index, atomForm body bodyForm (sourceBody index) := by
  unfold kernelPolynomial
  calc
    _ = ∑ colors : Fin r → Primary, ∑ centers : Fin s → Body,
        (∏ index, MvPolynomial.C (primary.weight (colors index) *
          Hoeffding.centeredAtom primary (sourcePrimary index) (colors index)) * primaryForm (colors index)) *
        (∏ index, MvPolynomial.C (body.weight (centers index) *
          Hoeffding.centeredAtom body (sourceBody index) (centers index)) * bodyForm (centers index)) := by
      apply Finset.sum_congr rfl
      intro colors _
      apply Finset.sum_congr rfl
      intro centers _
      simp only [pointTensor, map_mul, map_prod, Finset.prod_mul_distrib]
      ring
    _ = (∑ colors : Fin r → Primary,
        ∏ index, MvPolynomial.C (primary.weight (colors index) *
          Hoeffding.centeredAtom primary (sourcePrimary index) (colors index)) * primaryForm (colors index)) *
        (∑ centers : Fin s → Body,
        ∏ index, MvPolynomial.C (body.weight (centers index) *
          Hoeffding.centeredAtom body (sourceBody index) (centers index)) * bodyForm (centers index)) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply congrArg₂ (· * ·)
      · exact (Fintype.prod_sum (fun (index : Fin r) (output : Primary) =>
          MvPolynomial.C (primary.weight output * Hoeffding.centeredAtom primary (sourcePrimary index) output) *
            primaryForm output)).symm
      · exact (Fintype.prod_sum (fun (index : Fin s) (output : Body) =>
          MvPolynomial.C (body.weight output * Hoeffding.centeredAtom body (sourceBody index) output) *
            bodyForm output)).symm

theorem pointKernel_polynomial (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    (primaryForm : Primary → MvPolynomial Variable ℝ) (bodyForm : Body → MvPolynomial Variable ℝ)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    kernelPolynomial primary body primaryForm bodyForm
        (pointKernel primary body hprimary hbody sourcePrimary sourceBody).val =
      (∏ index, atomForm primary primaryForm (sourcePrimary index)) *
        ∏ index, atomForm body bodyForm (sourceBody index) := by
  change kernelPolynomial primary body primaryForm bodyForm
    (symmetrize (pointTensor primary body sourcePrimary sourceBody)) = _
  rw [kernelPolynomial_symmetrize, pointTensor_polynomial]

/-- Leading evaluation of an arbitrary joint canonical kernel equals its
actual reference average of products of the single-slot point responses.
This identity does not require leading evaluation to be injective. -/
theorem joint_polynomial_reconstruction (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    (primaryForm : Primary → MvPolynomial Variable ℝ) (bodyForm : Body → MvPolynomial Variable ℝ)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    kernelPolynomial primary body primaryForm bodyForm kernel.val =
      ∑ sourcePrimary, ∑ sourceBody,
        ((∏ index, primary.weight (sourcePrimary index)) *
          (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          ((∏ index, atomForm primary primaryForm (sourcePrimary index)) *
            ∏ index, atomForm body bodyForm (sourceBody index)) := by
  have hraw : (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          pointTensor primary body sourcePrimary sourceBody) = kernel.val := by
    funext colors centers
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact pointTensor_expansion primary body hprimary hbody kernel colors centers
  have h := congrArg (kernelLinear primary body primaryForm bodyForm) hraw
  simp only [map_sum, map_smul] at h
  change (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          kernelPolynomial primary body primaryForm bodyForm (pointTensor primary body sourcePrimary sourceBody)) =
    kernelPolynomial primary body primaryForm bodyForm kernel.val at h
  simp only [pointTensor_polynomial] at h
  exact h.symm

end

end CurrentAFT.PointPolynomial

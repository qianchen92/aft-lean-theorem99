import CurrentAFT.ControlProduct
import AFT.CanonicalPointBasis

/-!
# Actual two-alphabet canonical point reconstruction

Every joint kernel is kept intact in its finite reference sum. The two
slot families use their own reference laws. No product assumption on the
input kernel is made.
-/

namespace CurrentAFT.CanonicalReconstruction

open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def pointTensor {r s : ℕ} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    DensityKernel (Primary := Primary) (Body := Body) r s :=
  fun colors centers =>
    (∏ index, Hoeffding.centeredAtom primary (sourcePrimary index) (colors index)) *
      ∏ index, Hoeffding.centeredAtom body (sourceBody index) (centers index)

theorem indicator_basis_expansion (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    (∑ sourcePrimary, ∑ sourceBody,
      kernel.val sourcePrimary sourceBody *
        MixedKernel.canonicalPointBasis (fun _ : Fin r => primary) sourcePrimary colors *
          MixedKernel.canonicalPointBasis (fun _ : Fin s => body) sourceBody centers) =
      kernel.val colors centers := by
  have hprimary (fixed : Fin s → Body) :
      Hoeffding.Canonical (fun _ : Fin r => primary) Finset.univ (fun word => kernel.val word fixed) := by
    constructor
    · intro first second hequal
      have hword : first = second := funext fun index => hequal index (Finset.mem_univ index)
      rw [hword]
    · intro index _ word
      exact kernel.property.1 index word fixed
  have hbody (fixed : Fin r → Primary) :
      Hoeffding.Canonical (fun _ : Fin s => body) Finset.univ (kernel.val fixed) := by
    constructor
    · intro first second hequal
      have hword : first = second := funext fun index => hequal index (Finset.mem_univ index)
      rw [hword]
    · intro index _ word
      exact kernel.property.2.1 index fixed word
  have hp := MixedKernel.canonicalPointBasis_expansion (fun _ : Fin r => primary)
    (fun word => kernel.val word centers) (hprimary centers) colors
  have hb (source : Fin r → Primary) := MixedKernel.canonicalPointBasis_expansion
    (fun _ : Fin s => body) (kernel.val source) (hbody source) centers
  calc
    _ = ∑ sourcePrimary,
        (∑ sourceBody, kernel.val sourcePrimary sourceBody *
          MixedKernel.canonicalPointBasis (fun _ : Fin s => body) sourceBody centers) *
          MixedKernel.canonicalPointBasis (fun _ : Fin r => primary) sourcePrimary colors := by
      apply Finset.sum_congr rfl
      intro source _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro other _
      ring
    _ = _ := by simp only [hb]; exact hp

private theorem weighted_centeredAtom {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) (source output : Color) :
    law.weight source * Hoeffding.centeredAtom law source output =
      (if output = source then 1 else 0) - law.weight source := by
  by_cases hequal : source = output
  · subst output
    simp only [Hoeffding.centeredAtom, if_true, mul_sub, mul_one,
      mul_inv_cancel₀ (hpositive source).ne']
  · simp only [Hoeffding.centeredAtom, hequal, Ne.symm hequal, if_false, zero_sub, mul_neg, mul_one]

theorem weighted_basis_product {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) {Index : Type*} [Fintype Index] [DecidableEq Index]
    (source output : Index → Color) :
    (∏ index, law.weight (source index)) *
        (∏ index, Hoeffding.centeredAtom law (source index) (output index)) =
      MixedKernel.canonicalPointBasis (fun _ : Index => law) source output := by
  rw [← Finset.prod_mul_distrib]
  simp only [weighted_centeredAtom law hpositive, MixedKernel.canonicalPointBasis]

/-- The exact centered-Dirac expansion under the two actual product
references. This also covers degree zero and arbitrary joint kernels. -/
theorem pointTensor_expansion (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    {r s : ℕ} (kernel : canonicalKernels primary body r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) *
          pointTensor primary body sourcePrimary sourceBody colors centers) =
      kernel.val colors centers := by
  rw [← indicator_basis_expansion primary body kernel colors centers]
  apply Finset.sum_congr rfl
  intro sourcePrimary _
  apply Finset.sum_congr rfl
  intro sourceBody _
  rw [← weighted_basis_product primary hprimary, ← weighted_basis_product body hbody]
  unfold pointTensor
  ring

private theorem atomProduct_centered {Color Index : Type*} [Fintype Color] [Fintype Index]
    [DecidableEq Index] (law : FiniteDist Color) (hpositive : ∀ color, 0 < law.weight color)
    (source output : Index → Color) (fixed : Index) :
    (∑ color, law.weight color *
      ∏ index, Hoeffding.centeredAtom law (source index) (Function.update output fixed color index)) = 0 := by
  have hproduct (color : Color) :
      (∏ index, Hoeffding.centeredAtom law (source index) (Function.update output fixed color index)) =
        Hoeffding.centeredAtom law (source fixed) color *
          ∏ index ∈ Finset.univ.erase fixed, Hoeffding.centeredAtom law (source index) (output index) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ fixed), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro index hindex
    rw [Function.update_of_ne (Finset.mem_erase.mp hindex).1]
  simp only [hproduct, ← mul_assoc, ← Finset.sum_mul,
    Hoeffding.centeredAtom_mean law hpositive, zero_mul]

theorem pointTensor_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    pointTensor primary body sourcePrimary sourceBody ∈ centeredKernelSpace primary body := by
  constructor
  · intro index colors centers
    simp only [pointTensor, ← mul_assoc, ← Finset.sum_mul,
      atomProduct_centered primary hprimary sourcePrimary colors index, zero_mul]
  · intro index colors centers
    simp only [pointTensor]
    calc
      _ = (∏ primaryIndex, Hoeffding.centeredAtom primary (sourcePrimary primaryIndex) (colors primaryIndex)) *
          ∑ color, body.weight color *
            ∏ bodyIndex, Hoeffding.centeredAtom body (sourceBody bodyIndex) (Function.update centers index color bodyIndex) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        ring
      _ = 0 := by rw [atomProduct_centered body hbody sourceBody centers index, mul_zero]

def pointKernel (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    canonicalKernels primary body r s := by
  let raw := pointTensor primary body sourcePrimary sourceBody
  have hcenter := symmetrize_centered primary body raw
    (pointTensor_centered primary body hprimary hbody sourcePrimary sourceBody)
  refine ⟨symmetrize raw, hcenter.1, hcenter.2, ?_⟩
  intro primaryOrder bodyOrder colors centers
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]

/-- Symmetrizing the actual finite centered-point expansion reconstructs
the entire original canonical fiber, with all joint dependencies retained. -/
theorem pointKernel_expansion (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          pointKernel primary body hprimary hbody sourcePrimary sourceBody) = kernel := by
  have hraw : (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          pointTensor primary body sourcePrimary sourceBody) = kernel.val := by
    funext colors centers
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact pointTensor_expansion primary body hprimary hbody kernel colors centers
  have hsymmetric : symmetrize kernel.val = kernel.val :=
    symmetrize_of_symmetric kernel.val kernel.property.2.2
  have h := congrArg (symmetrizeLinear (Primary := Primary) (Body := Body)) hraw
  simp only [map_sum, map_smul] at h
  change (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          symmetrize (pointTensor primary body sourcePrimary sourceBody)) = symmetrize kernel.val at h
  rw [hsymmetric] at h
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul, pointKernel] using h

end

end CurrentAFT.CanonicalReconstruction

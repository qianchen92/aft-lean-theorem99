import CurrentAFT.RootLegCoefficientNorm

/-! # Actual local responses are linear in the common public score -/
namespace CurrentAFT.RootLegCoefficientLinear

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse RootLegCoefficientFamily
open scoped BigOperators Classical

noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

def selectedDensityLinear (security degree : ℕ) (selected : Finset (Fin 3))
    (hdegree : Fintype.card selected = degree) :
    ((Fin 3 → Palette security) → ℝ) →ₗ[ℝ] ((Fin degree → Palette security) → ℝ) where
  toFun := fun mass => selectedDensity security degree mass selected hdegree
  map_add' first second := by
    funext word
    simp only [selectedDensity, LocalTensors.referenceRestrictedComponent, Pi.add_apply,
      add_mul, Finset.sum_add_distrib]
  map_smul' scalar mass := by
    funext word
    simp only [selectedDensity, LocalTensors.referenceRestrictedComponent, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

def normalizedSelectedLinear (security degree : ℕ) (selected : Finset (Fin 3))
    (hdegree : Fintype.card selected = degree) :=
  (PrimaryTensorInverse.tensorInverse security degree).comp (selectedDensityLinear security degree selected hdegree)

def selectedKernelLinear (security degree : ℕ) (selected : Finset (Fin 3))
    (hdegree : Fintype.card selected = degree) :
    ((Fin 3 → Palette security) → ℝ) →ₗ[ℝ]
      canonicalKernels (primaryLaw security) (bodyReference security) degree 0 where
  toFun := fun mass => selectedKernel security degree mass selected hdegree
  map_add' first second := by
    apply Subtype.ext
    have hraw : (fun colors (_ : Fin 0 → SafePalette security) =>
        normalizedSelectedDensity security degree (first + second) selected hdegree colors) =
        (fun colors (_ : Fin 0 → SafePalette security) => normalizedSelectedDensity security degree first selected hdegree colors) +
        (fun colors (_ : Fin 0 → SafePalette security) => normalizedSelectedDensity security degree second selected hdegree colors) := by
      funext colors _
      exact congrFun ((normalizedSelectedLinear security degree selected hdegree).map_add first second) colors
    change ControlProduct.symmetrize _ = ControlProduct.symmetrize _ + ControlProduct.symmetrize _
    rw [hraw]
    exact (symmetrizeLinear (PS := Fin degree) (BS := Fin 0)).map_add _ _
  map_smul' scalar mass := by
    apply Subtype.ext
    have hraw : (fun colors (_ : Fin 0 → SafePalette security) =>
        normalizedSelectedDensity security degree (scalar • mass) selected hdegree colors) =
        scalar • (fun colors (_ : Fin 0 → SafePalette security) =>
          normalizedSelectedDensity security degree mass selected hdegree colors) := by
      funext colors _
      exact congrFun ((normalizedSelectedLinear security degree selected hdegree).map_smul scalar mass) colors
    change ControlProduct.symmetrize _ = scalar • ControlProduct.symmetrize _
    rw [hraw]
    exact (symmetrizeLinear (PS := Fin degree) (BS := Fin 0)).map_smul scalar _

def selectedFamilyLinear (security order : ℕ) (selected : Finset (Fin 3)) :
    ((Fin 3 → Palette security) → ℝ) →ₗ[ℝ] Family security order where
  toFun := fun mass => selectedFamily security order mass selected
  map_add' first second := by
    unfold selectedFamily
    split_ifs with hdegree
    · have hkernel := (selectedKernelLinear security selected.card selected (by simp)).map_add first second
      funext arity
      by_cases hequal : arity = selectedArity order selected hdegree
      · subst arity
        simp only [Pi.add_apply, Pi.single_eq_same]
        exact hkernel
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hequal, add_zero]
    · exact (add_zero _).symm
  map_smul' scalar mass := by
    unfold selectedFamily
    split_ifs with hdegree
    · have hkernel := (selectedKernelLinear security selected.card selected (by simp)).map_smul scalar mass
      funext arity
      by_cases hequal : arity = selectedArity order selected hdegree
      · subst arity
        simp only [Pi.smul_apply, Pi.single_eq_same]
        exact hkernel
      · simp only [Pi.smul_apply, Pi.single_eq_of_ne hequal, smul_zero]
    · exact (smul_zero _).symm


def higherFamilyLinear (security order : ℕ) :
    ((Fin 3 → Palette security) → ℝ) →ₗ[ℝ] Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
    selectedFamilyLinear security order selected

theorem higherFamilyLinear_apply (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ) :
    higherFamilyLinear security order mass = higherFamily security order mass := by
  simp only [higherFamilyLinear, LinearMap.sum_apply, higherFamily, selectedFamilyLinear,
    LinearMap.coe_mk, AddHom.coe_mk]

def rootHigherLinear (security order : ℕ) :
    (CycleRootExpansion.Root security → ℝ) →ₗ[ℝ] Family security order :=
  (higherFamilyLinear security order).comp (RootTaggedLegHigher.massLinear security)

theorem rootHigherLinear_apply (security order : ℕ) (input : CycleRootExpansion.Root security → ℝ) :
    rootHigherLinear security order input = rootHigherFamily security order input := by
  rw [rootHigherLinear, LinearMap.comp_apply, higherFamilyLinear_apply]
  rfl

end

end CurrentAFT.RootLegCoefficientLinear

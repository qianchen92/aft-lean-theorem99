import CurrentAFT.LocalRaisingFirst

/-! # Actual local responses are linear in the common public score -/
namespace CurrentAFT.LocalRaisingLinear

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily NormalizedLocalPolynomial LocalRaisingFirst
open scoped BigOperators Classical

noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

def selectedDensityLinear (security degree : ℕ) (selected : Finset (Fin 4))
    (hdegree : Fintype.card selected = degree) :
    ((Fin 4 → Palette security) → ℝ) →ₗ[ℝ] ((Fin degree → Palette security) → ℝ) where
  toFun := fun mass => selectedDensity security degree mass selected hdegree
  map_add' first second := by
    funext word
    simp only [selectedDensity, LocalTensors.referenceRestrictedComponent, Pi.add_apply,
      add_mul, Finset.sum_add_distrib]
  map_smul' scalar mass := by
    funext word
    simp only [selectedDensity, LocalTensors.referenceRestrictedComponent, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

def normalizedSelectedLinear (security degree : ℕ) (selected : Finset (Fin 4))
    (hdegree : Fintype.card selected = degree) :=
  (PrimaryTensorInverse.tensorInverse security degree).comp (selectedDensityLinear security degree selected hdegree)

def selectedKernelLinear (security degree : ℕ) (selected : Finset (Fin 4))
    (hdegree : Fintype.card selected = degree) :
    ((Fin 4 → Palette security) → ℝ) →ₗ[ℝ]
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

def selectedFamilyLinear (security order : ℕ) (selected : Finset (Fin 4)) :
    ((Fin 4 → Palette security) → ℝ) →ₗ[ℝ] Family security order where
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

def completeFamilyLinear (security order : ℕ) :
    ((Fin 4 → Palette security) → ℝ) →ₗ[ℝ] Family security order where
  toFun := completeFamily security order
  map_add' first second := by
    unfold completeFamily
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_smul]
    simp only [show ∀ selected, selectedFamily security order (first + second) selected =
      selectedFamily security order first selected + selectedFamily security order second selected from
        fun selected => (selectedFamilyLinear security order selected).map_add first second,
      Finset.sum_add_distrib]
    abel
  map_smul' scalar mass := by
    unfold completeFamily
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_smul]
    simp only [show ∀ selected, selectedFamily security order (scalar • mass) selected =
      scalar • selectedFamily security order mass selected from
        fun selected => (selectedFamilyLinear security order selected).map_smul scalar mass,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

def independentSignedLinear (security : ℕ) :
    (Palette security → ℝ) →ₗ[ℝ] ((Fin 4 → Palette security) → ℝ) where
  toFun := IndependentPairedReference.independentSignedMass security
  map_add' first second := by
    funext word
    simp only [IndependentPairedReference.independentSignedMass, map_add, Pi.add_apply,
      mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar score := by
    funext word
    simp only [IndependentPairedReference.independentSignedMass, map_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro group _
    ring

def independentNormalizedLinear (security order : ℕ) :
    (Palette security → ℝ) →ₗ[ℝ] Family security order where
  toFun := independentNormalized security order
  map_add' first second := by
    unfold independentNormalized normalizedFamily
    rw [show IndependentPairedReference.independentSignedMass security (first + second) =
      IndependentPairedReference.independentSignedMass security first +
      IndependentPairedReference.independentSignedMass security second from
        (independentSignedLinear security).map_add first second]
    rw [show completeFamily security order
      (IndependentPairedReference.independentSignedMass security first +
        IndependentPairedReference.independentSignedMass security second) =
      completeFamily security order (IndependentPairedReference.independentSignedMass security first) +
      completeFamily security order (IndependentPairedReference.independentSignedMass security second) from
        (completeFamilyLinear security order).map_add _ _, add_mul]
  map_smul' scalar score := by
    unfold independentNormalized normalizedFamily
    rw [show IndependentPairedReference.independentSignedMass security (scalar • score) =
      scalar • IndependentPairedReference.independentSignedMass security score from
        (independentSignedLinear security).map_smul scalar score]
    rw [show completeFamily security order (scalar • IndependentPairedReference.independentSignedMass security score) =
      scalar • completeFamily security order (IndependentPairedReference.independentSignedMass security score) from
        (completeFamilyLinear security order).map_smul scalar _, smul_mul_assoc, RingHom.id_apply]

/-- A score is centered once relative to the common primary law, independently
of every hidden root and every choice of distinct public-control indices. -/
def centeredScores (security : ℕ) : Submodule ℝ (Palette security → ℝ) where
  carrier := {score | (primaryLaw security).expectation score = 0}
  zero_mem' := by simp [FiniteDist.expectation]
  add_mem' {first second} hfirst hsecond := by
    change (primaryLaw security).expectation first = 0 at hfirst
    change (primaryLaw security).expectation second = 0 at hsecond
    change (primaryLaw security).expectation (fun color => first color + second color) = 0
    rw [FiniteDist.expectation_add, hfirst, hsecond, add_zero]
  smul_mem' scalar score hscore := by
    change (primaryLaw security).expectation (fun color => scalar * score color) = 0
    rw [FiniteDist.expectation_const_mul, hscore, mul_zero]

def primaryEmbeddingLinear (security order : ℕ) (horder : 1 ≤ order) :
    centeredScores security →ₗ[ℝ] Family security order where
  toFun := fun score => BackgroundFamilies.primaryFamily (primaryLaw security) (bodyReference security)
    order horder score.val score.property
  map_add' first second := by
    unfold BackgroundFamilies.primaryFamily
    rw [← Pi.single_add]
    rfl
  map_smul' scalar score := by
    unfold BackgroundFamilies.primaryFamily
    rw [← Pi.single_smul]
    rfl

def localRaisingLinear (security order : ℕ) (horder : 1 ≤ order) :
    centeredScores security →ₗ[ℝ] Family security order :=
  (independentNormalizedLinear security order).comp (centeredScores security).subtype -
    primaryEmbeddingLinear security order horder

theorem localRaisingLinear_apply (security order : ℕ) (horder : 1 ≤ order) (score : centeredScores security) :
    localRaisingLinear security order horder score = localRaising security order horder score.val score.property := rfl

theorem localRaisingLinear_vanishesBelow (security order : ℕ) (horder : 1 ≤ order)
    (score : centeredScores security) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (localRaisingLinear security order horder score) :=
  localRaising_vanishesBelow security order horder score.val score.property

end
end CurrentAFT.LocalRaisingLinear

import CurrentAFT.RootLegCoefficientLinear
import CurrentAFT.BackgroundEvaluation

/-! Exact physical polynomial images of the actual unselected leg coefficients. -/
namespace CurrentAFT.RootLegCoefficientEvaluation
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  LocalCoefficientEvaluation RootLegCoefficientFamily LeadingEvaluation
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security
theorem selectedKernel_polynomial (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ) :
    kernelPolynomial (primaryLaw security) (bodyReference security) (primaryForm security) bodyForms
      (selectedKernel security degree mass selected hdegree).val =
        RepresentedPolynomial.referenceCoefficientForm (primaryLaw security)
          (LocalReferenceEnergy.uniformReference security) mass selected := by
  change kernelPolynomial (primaryLaw security) (bodyReference security) (primaryForm security) bodyForms
    (symmetrize (fun colors (_ : Fin 0 → SafePalette security) =>
      normalizedSelectedDensity security degree mass selected hdegree colors)) = _
  rw [kernelPolynomial_symmetrize, primary_kernelPolynomial, normalizedSelectedDensity_polynomial]
theorem selectedFamily_image (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3))
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    evaluation security order bodyForms hbody (selectedFamily security order mass selected) =
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.referenceCoefficientForm (primaryLaw security)
          (LocalReferenceEnergy.uniformReference security) mass selected) := by
  unfold selectedFamily
  split_ifs with hdegree
  · change LeadingEvaluation.familyLinear _ _ _ _ _ (Pi.single _ _) = _
    rw [LeadingEvaluation.familyLinear_single]
    change TruncatedOutput.quotientMap order (kernelPolynomial (primaryLaw security) (bodyReference security)
      (primaryForm security) bodyForms (selectedKernel security selected.card mass selected (by simp)).val) = _
    rw [selectedKernel_polynomial]
  · rw [map_zero]
    have hzero := LeadingEvaluation.homogeneousLinear_above (primaryLaw security) (bodyReference security)
      (primaryForm security) bodyForms (primaryForm_homogeneous security) hbody order selected.card 0 (by omega)
      (selectedKernel security selected.card mass selected (by simp))
    change TruncatedOutput.quotientMap order (kernelPolynomial (primaryLaw security) (bodyReference security)
      (primaryForm security) bodyForms (selectedKernel security selected.card mass selected (by simp)).val) = 0 at hzero
    rw [selectedKernel_polynomial] at hzero
    exact hzero.symm

theorem higherFamily_image (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    evaluation security order bodyForms hbody (higherFamily security order mass) =
      TruncatedOutput.quotientMap order
        (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
          RepresentedPolynomial.referenceCoefficientForm (primaryLaw security)
            (LocalReferenceEnergy.uniformReference security) mass selected) := by
  unfold higherFamily
  simp only [map_sum, selectedFamily_image]

end
end CurrentAFT.RootLegCoefficientEvaluation

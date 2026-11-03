import CurrentAFT.LocalCoefficientFamily
import CurrentAFT.FamilyEvaluation
import AFT.TensorChannelFormula

/-! # Exact polynomial evaluation of the current normalized local coefficients -/

namespace CurrentAFT.LocalCoefficientEvaluation

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open LocalCoefficientFamily LeadingEvaluation
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

def densityPolynomial {Color Variable : Type*} [Fintype Color] (primary : FiniteDist Color)
    (forms : Color → MvPolynomial Variable ℝ) (degree : ℕ) (density : (Fin degree → Color) → ℝ) :
    MvPolynomial Variable ℝ :=
  ∑ word, MvPolynomial.C ((∏ index, primary.weight (word index)) * density word) *
    ∏ index, forms (word index)

def channelForm {Color : Type*} [Fintype Color] (primary : FiniteDist Color)
    (channel : (Color → ℝ) →ₗ[ℝ] (Color → ℝ)) (input : Color) : MvPolynomial Color ℝ :=
  ∑ output, MvPolynomial.C (primary.weight output * channel (Pi.single input 1) output / primary.weight input) *
    MvPolynomial.X output

/-- Exact weighted tensor adjunction, proved from the literal finite
matrix of the channel. No polynomial-image identity is assumed. -/
theorem channelForm_tensor {Color : Type*} [Fintype Color] (primary : FiniteDist Color)
    (hpositive : ∀ color, primary.weight color ≠ 0)
    (channel : (Color → ℝ) →ₗ[ℝ] (Color → ℝ)) (degree : ℕ) (density : (Fin degree → Color) → ℝ) :
    densityPolynomial primary (channelForm primary channel) degree density =
      densityPolynomial primary MvPolynomial.X degree (TensorChannel.apply degree (fun _ => channel) density) := by
  classical
  unfold densityPolynomial
  simp_rw [TensorChannel.apply_formula_instance]
  simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  unfold channelForm
  rw [Fintype.prod_sum (fun index : Fin degree => fun output : Color =>
    MvPolynomial.C (primary.weight output * channel (Pi.single (input index) 1) output / primary.weight (input index)) *
      MvPolynomial.X output)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _
  rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]
  congr 1
  congr 1
  have hproduct : (∏ index, primary.weight (input index)) *
      (∏ index, primary.weight (output index) * channel (Pi.single (input index) 1) (output index) /
        primary.weight (input index)) =
      (∏ index, primary.weight (output index)) *
        ∏ index, channel (Pi.single (input index) 1) (output index) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro index _
    field_simp [hpositive (input index)]
  calc
    _ = density input * ((∏ index, primary.weight (input index)) *
        ∏ index, primary.weight (output index) * channel (Pi.single (input index) 1) (output index) /
          primary.weight (input index)) := by ring
    _ = _ := by rw [hproduct]; ring

def primaryForm (security : ℕ) : Palette security → MvPolynomial (Palette security) ℝ :=
  channelForm (primaryLaw security) (PrimaryTensorInverse.densityResponse security)

theorem primaryForm_homogeneous (security : ℕ) (input : Palette security) :
    (primaryForm security input).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro output _
  exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X ℝ output)

/-- The weighted density-channel column is the actual mass-coordinate
first response of a Dirac input, with its genuine activation. -/
theorem primaryForm_physical (security : ℕ) (input : Palette security) :
    primaryForm security input = RepresentedPolynomial.profileForm
      (fun output => activation security * FirstResponse.response security (Pi.single input 1) output) := by
  classical
  have hdelta : (fun color : Palette security => (primaryLaw security).weight color *
      (Pi.single input (1 : ℝ) : Palette security → ℝ) color) =
      (primaryLaw security).weight input • (Pi.single input (1 : ℝ) : Palette security → ℝ) := by
    funext color
    by_cases hequal : color = input
    · subst color
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    · simp only [Pi.single_eq_of_ne hequal, mul_zero, Pi.smul_apply, smul_eq_mul]
  unfold primaryForm channelForm
  rw [RepresentedPolynomial.profileForm_apply]
  apply Finset.sum_congr rfl
  intro output _
  rw [PrimaryTensorInverse.densityResponse_apply, hdelta, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  field_simp [(primaryReference_positive security input).ne', (primaryReference_positive security output).ne']

theorem kernelPolynomial_no_body {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (forms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (degree : ℕ) (density : (Fin degree → Primary) → ℝ) :
    kernelPolynomial primary body forms bodyForms (fun colors (_ : Fin 0 → Body) => density colors) =
      densityPolynomial primary forms degree density := by
  simp only [kernelPolynomial, densityPolynomial, Fin.prod_univ_zero, Fintype.sum_unique, mul_one]

theorem primary_kernelPolynomial (security degree : ℕ) (density : (Fin degree → Palette security) → ℝ)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ) :
    kernelPolynomial (primaryLaw security) (bodyReference security) (primaryForm security) bodyForms
      (fun colors (_ : Fin 0 → SafePalette security) => density colors) =
        primaryLeadingPolynomial security degree density := by
  rw [kernelPolynomial_no_body, primaryForm,
    channelForm_tensor (primaryLaw security) (fun color => (primaryReference_positive security color).ne')]
  rfl

/-- The genuinely symmetrized current coefficient has exactly the
selected physical PGF image under the actual first-response forms. -/
theorem selectedKernel_polynomial (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ) :
    kernelPolynomial (primaryLaw security) (bodyReference security) (primaryForm security) bodyForms
      (selectedKernel security degree mass selected hdegree).val =
        RepresentedPolynomial.referenceCoefficientForm (primaryLaw security)
          (LocalReferenceEnergy.uniformReference security) mass selected := by
  change kernelPolynomial (primaryLaw security) (bodyReference security) (primaryForm security) bodyForms
    (symmetrize (fun colors (_ : Fin 0 → SafePalette security) =>
      normalizedSelectedDensity security degree mass selected hdegree colors)) = _
  rw [kernelPolynomial_symmetrize, primary_kernelPolynomial, normalizedSelectedDensity_polynomial]

def evaluation (security order : ℕ)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :=
  LeadingEvaluation.familyHom (primaryLaw security) (bodyReference security) (primaryForm security) bodyForms
    (primaryForm_homogeneous security) hbody order

theorem selectedFamily_image (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4))
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

theorem higherFamily_image (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    evaluation security order bodyForms hbody (higherFamily security order mass) =
      TruncatedOutput.quotientMap order
        (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card),
          RepresentedPolynomial.referenceCoefficientForm (primaryLaw security)
            (LocalReferenceEnergy.uniformReference security) mass selected) := by
  unfold higherFamily
  simp only [map_sum, selectedFamily_image]

end

end CurrentAFT.LocalCoefficientEvaluation

import CurrentAFT.BackgroundEvaluation

/-! Literal degree-one primary evaluation for the concrete background certificates. -/

namespace CurrentAFT.BackgroundFirstEvaluation

open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation
  LocalCoefficientFamily LocalCoefficientEvaluation FringeCertificate BackgroundTranslations
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem primaryKernel_polynomial {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    kernelPolynomial primary body primaryForms bodyForms (primaryKernel primary body density hcenter).val =
      densityPolynomial primary primaryForms 1 (oneWordProfile density) :=
  kernelPolynomial_no_body primary body primaryForms bodyForms 1 (oneWordProfile density)

theorem primaryFamily_generic_image {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForms color).IsHomogeneous 1) (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 1 ≤ order) (density : Primary → ℝ)
    (hcenter : ∑ color, primary.weight color * density color = 0) :
    familyHom primary body primaryForms bodyForms hprimary hbody order
      (primaryFamily primary body order horder density hcenter) =
        TruncatedOutput.quotientMap order (densityPolynomial primary primaryForms 1 (oneWordProfile density)) := by
  change familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [familyLinear_single]
  change TruncatedOutput.quotientMap order (kernelPolynomial primary body primaryForms bodyForms
    (primaryKernel primary body density hcenter).val) = _
  rw [primaryKernel_polynomial]

theorem massPolynomial_one (security : ℕ) (profile : ActualControls.Palette security → ℝ) :
    massPolynomial security 1 (oneWordProfile profile) = RepresentedPolynomial.profileForm profile := by
  rw [RepresentedPolynomial.profileForm_apply]
  unfold massPolynomial
  simp only [oneWordProfile, Fin.prod_univ_one]
  exact ((Equiv.funUnique (Fin 1) (ActualControls.Palette security)).symm.sum_comp
    (fun word : Fin 1 → ActualControls.Palette security => MvPolynomial.C (profile (word 0)) * MvPolynomial.X (word 0))).symm

theorem massLeading_one (security : ℕ) (density : ActualControls.Palette security → ℝ) :
    massLeading security 1 (oneWordProfile density) =
      oneWordProfile (activation security • FirstResponse.response security
        (fun color => (primaryLaw security).weight color * density color)) := by
  funext word
  have hresponse : tensorResponse security 1 (oneWordProfile density) word = densityResponse security density (word 0) := rfl
  rw [massLeading, hresponse, referenceWeight, Fin.prod_univ_one, densityResponse_apply]
  simp only [oneWordProfile, Pi.smul_apply, smul_eq_mul]
  field_simp [(primaryReference_positive security (word 0)).ne']

theorem primaryFamily_image_with_forms (security order : ℕ) (horder : 1 ≤ order)
    (bodyForms : SafePalette security → MvPolynomial (ActualControls.Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (density : ActualControls.Palette security → ℝ)
    (hcenter : ∑ color, (primaryLaw security).weight color * density color = 0) :
    LocalCoefficientEvaluation.evaluation security order bodyForms hbody
      (primaryFamily (primaryLaw security) (bodyReference security) order horder density hcenter) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm
        (activation security • FirstResponse.response security (fun color => (primaryLaw security).weight color * density color))) := by
  have h := primaryFamily_generic_image (primaryLaw security) (bodyReference security) (primaryForm security) bodyForms
    (primaryForm_homogeneous security) hbody order horder density hcenter
  have hpoly := primary_kernelPolynomial security 1 (oneWordProfile density) bodyForms
  rw [kernelPolynomial_no_body] at hpoly
  rw [hpoly] at h
  unfold primaryLeadingPolynomial at h
  rw [massLeading_one, massPolynomial_one] at h
  exact h


theorem primaryFamily_image (security order : ℕ) (horder : 1 ≤ order)
    (density : ActualControls.Palette security → ℝ)
    (hcenter : ∑ color, (primaryLaw security).weight color * density color = 0) :
    BackgroundEvaluation.evaluation security order
      (primaryFamily (primaryLaw security) (bodyReference security) order horder density hcenter) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm
        (activation security • FirstResponse.response security (fun color => (primaryLaw security).weight color * density color))) :=
  primaryFamily_image_with_forms security order horder (bodyForm security) (bodyForm_homogeneous security) density hcenter

theorem fringePrimary_image (security order : ℕ) (horder : 1 ≤ order) :
    BackgroundEvaluation.evaluation security order
      (primaryFamily (primaryLaw security) (bodyReference security) order horder
        (primaryCertificateDensity security) (primaryCertificateDensity_centered security)) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm (bodyDeviation security)) := by
  rw [primaryFamily_image, primaryCertificateDensity_leading]

theorem translationResidual_image (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    BackgroundEvaluation.evaluation security order
      (primaryFamily (primaryLaw security) (bodyReference security) order horder
        (residualCertificateDensity security shift) (residualCertificateDensity_centered security shift)) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm (translationResidual security shift)) := by
  rw [primaryFamily_image, residualCertificateDensity_leading]

end

end CurrentAFT.BackgroundFirstEvaluation

import CurrentAFT.BackgroundFirstEvaluation

/-! Exact rectangular weighted tensor adjunction for actual safe-body channels. -/

namespace CurrentAFT.BodyChannelEvaluation

open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation BackgroundFirstEvaluation
  MarkedPairLeading LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference MarkedPairLeading.bodyConvolution

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def rectangularForm {Input Output : Type*} [Fintype Output]
    (input : Input → ℝ) (output : Output → ℝ)
    (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (point : Input) : MvPolynomial Output ℝ :=
  ∑ value, MvPolynomial.C (output value * channel (Pi.single point 1) value / input point) * MvPolynomial.X value

theorem rectangular_tensor_adjoint {Input Output : Type*} [Fintype Input] [Fintype Output]
    (input : FiniteDist Input) (output : FiniteDist Output) (hpositive : ∀ point, input.weight point ≠ 0)
    (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (degree : ℕ) (density : (Fin degree → Input) → ℝ) :
    densityPolynomial input (rectangularForm input.weight output.weight channel) degree density =
      densityPolynomial output MvPolynomial.X degree (TensorChannel.apply degree (fun _ => channel) density) := by
  unfold densityPolynomial
  simp_rw [TensorChannel.apply_formula_instance]
  simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro point _
  unfold rectangularForm
  rw [Fintype.prod_sum (fun index : Fin degree => fun value : Output =>
    MvPolynomial.C (output.weight value * channel (Pi.single (point index) 1) value / input.weight (point index)) * MvPolynomial.X value)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]
  congr 1
  congr 1
  have hproduct : (∏ index, input.weight (point index)) *
      (∏ index, output.weight (value index) * channel (Pi.single (point index) 1) (value index) / input.weight (point index)) =
      (∏ index, output.weight (value index)) * ∏ index, channel (Pi.single (point index) 1) (value index) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro index _
    field_simp [hpositive (point index)]
  calc
    _ = density point * ((∏ index, input.weight (point index)) *
        ∏ index, output.weight (value index) * channel (Pi.single (point index) 1) (value index) / input.weight (point index)) := by ring
    _ = _ := by rw [hproduct]; ring

def weightedEmbedding {Input Output : Type*} [Fintype Input] (input : FiniteDist Input) (embedding : Input → Output) :
    (Input → ℝ) →ₗ[ℝ] (Output → ℝ) where
  toFun density := fun output => ∑ point, input.weight point * density point * (Pi.single (embedding point) (1 : ℝ) : Output → ℝ) output
  map_add' first second := by
    funext output
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar density := by
    funext output
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro point _
    ring

theorem weightedEmbedding_single {Input Output : Type*} [Fintype Input]
    (input : FiniteDist Input) (embedding : Input → Output) (point : Input) :
    weightedEmbedding input embedding (Pi.single point (1 : ℝ) : Input → ℝ) = input.weight point • (Pi.single (embedding point) (1 : ℝ) : Output → ℝ) := by
  funext output
  change (∑ other, input.weight other * (Pi.single point (1 : ℝ) : Input → ℝ) other *
    (Pi.single (embedding other) (1 : ℝ) : Output → ℝ) output) =
      input.weight point * (Pi.single (embedding point) (1 : ℝ) : Output → ℝ) output
  rw [Finset.sum_eq_single point]
  · simp only [Pi.single_eq_same, mul_one]
  · intro other _ hne
    simp only [Pi.single_eq_of_ne hne, mul_zero, zero_mul]
  · simp

def safeMass (security : ℕ) : (SafePalette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  weightedEmbedding (bodyReference security) Subtype.val

def bodyDensityChannel (security : ℕ) :
    (SafePalette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  (diagonal (fun output => ((primaryLaw security).weight output)⁻¹)).comp
    ((bodyConvolution security).comp (safeMass security))

theorem bodyDensityChannel_apply (security : ℕ) (density : SafePalette security → ℝ) (output : ActualControls.Palette security) :
    bodyDensityChannel security density output = bodyConvolution security (safeMass security density) output /
      (primaryLaw security).weight output := by
  simp only [bodyDensityChannel, LinearMap.comp_apply, diagonal, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem bodyForm_rectangular (security : ℕ) (point : SafePalette security) :
    bodyForm security point = rectangularForm (bodyReference security).weight (primaryLaw security).weight
      (bodyDensityChannel security) point := by
  rw [bodyForm, RepresentedPolynomial.profileForm_apply]
  unfold rectangularForm
  apply Finset.sum_congr rfl
  intro output _
  congr 1
  congr 1
  rw [bodyDensityChannel_apply, safeMass, weightedEmbedding_single, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [(primaryReference_positive security output).ne', (bodyReference_positive security point).ne']

def bodyTensorMass (security degree : ℕ) (density : (Fin degree → SafePalette security) → ℝ) :
    (Fin degree → ActualControls.Palette security) → ℝ :=
  fun output => referenceWeight security degree output * TensorChannel.apply degree (fun _ => bodyDensityChannel security) density output

theorem bodyTensor_polynomial (security degree : ℕ) (density : (Fin degree → SafePalette security) → ℝ) :
    densityPolynomial (bodyReference security) (bodyForm security) degree density =
      massPolynomial security degree (bodyTensorMass security degree density) := by
  have hforms : bodyForm security = rectangularForm (bodyReference security).weight (primaryLaw security).weight (bodyDensityChannel security) :=
    funext (bodyForm_rectangular security)
  rw [hforms, rectangular_tensor_adjoint (bodyReference security) (primaryLaw security)
    (fun point => (bodyReference_positive security point).ne')]
  rfl

theorem bodyKernel_polynomial {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Body → ℝ) (hcenter : ∑ color, body.weight color * density color = 0) :
    kernelPolynomial primary body primaryForms bodyForms (bodyKernel primary body density hcenter).val =
      densityPolynomial body bodyForms 1 (oneWordProfile density) := by
  simp only [kernelPolynomial, bodyKernel, densityPolynomial, oneWordProfile, Fin.prod_univ_zero,
    Fintype.sum_unique, one_mul]

theorem bodyFamily_generic_image {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForms color).IsHomogeneous 1) (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 1 ≤ order) (density : Body → ℝ)
    (hcenter : ∑ color, body.weight color * density color = 0) :
    familyHom primary body primaryForms bodyForms hprimary hbody order
      (bodyFamily primary body order horder density hcenter) =
        TruncatedOutput.quotientMap order (densityPolynomial body bodyForms 1 (oneWordProfile density)) := by
  change familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [familyLinear_single]
  change TruncatedOutput.quotientMap order (kernelPolynomial primary body primaryForms bodyForms
    (bodyKernel primary body density hcenter).val) = _
  rw [bodyKernel_polynomial]

theorem bodyTensorMass_one (security : ℕ) (density : SafePalette security → ℝ) :
    bodyTensorMass security 1 (oneWordProfile density) =
      oneWordProfile (bodyConvolution security (safeMass security density)) := by
  funext word
  have hresponse : TensorChannel.apply 1 (fun _ => bodyDensityChannel security) (oneWordProfile density) word =
      bodyDensityChannel security density (word 0) := rfl
  rw [bodyTensorMass, hresponse, referenceWeight, Fin.prod_univ_one, bodyDensityChannel_apply]
  unfold oneWordProfile
  field_simp [(primaryReference_positive security (word 0)).ne']

theorem bodyFamily_image (security order : ℕ) (horder : 1 ≤ order) (density : SafePalette security → ℝ)
    (hcenter : ∑ color, (bodyReference security).weight color * density color = 0) :
    BackgroundEvaluation.evaluation security order
      (bodyFamily (primaryLaw security) (bodyReference security) order horder density hcenter) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm (bodyConvolution security (safeMass security density))) := by
  have h := bodyFamily_generic_image (primaryLaw security) (bodyReference security) (primaryForm security) (bodyForm security)
    (primaryForm_homogeneous security) (bodyForm_homogeneous security) order horder density hcenter
  rw [bodyTensor_polynomial, bodyTensorMass_one, massPolynomial_one] at h
  exact h

theorem weightedEmbedding_supported {State : Type*} [Fintype State] (law : FiniteDist State) (safe : State → Prop)
    (hzero : ∀ state, ¬safe state → law.weight state = 0) (density : State → ℝ) :
    weightedEmbedding (supportedLaw law safe hzero) Subtype.val (fun point => density point.val) =
      fun state => law.weight state * density state := by
  funext output
  calc
    _ = (supportedLaw law safe hzero).expectation (fun point => density point.val * (Pi.single point.val (1 : ℝ) : State → ℝ) output) := by
      unfold weightedEmbedding FiniteDist.expectation
      apply Finset.sum_congr rfl
      intro point _
      ring
    _ = law.expectation (fun point => density point * (Pi.single point (1 : ℝ) : State → ℝ) output) := supportedLaw_expectation law safe hzero
      (fun point : State => density point * (Pi.single point (1 : ℝ) : State → ℝ) output)
    _ = _ := by simp [FiniteDist.expectation, Pi.single_apply]

theorem safeMass_full (security : ℕ) (density : ActualControls.Palette security → ℝ) :
    safeMass security (fun point => density point.val) = fun color => (centerLaw security).weight color * density color := by
  unfold safeMass bodyReference
  exact weightedEmbedding_supported _ _ _ density

theorem bodyConvolution_density (security : ℕ) (density : ActualControls.Palette security → ℝ) :
    bodyConvolution security (fun color => (centerLaw security).weight color * density color) =
      BackgroundCertificates.bodyLeadingResponse security density := by
  unfold bodyConvolution BackgroundCertificates.bodyLeadingResponse
  rfl

end

end CurrentAFT.BodyChannelEvaluation

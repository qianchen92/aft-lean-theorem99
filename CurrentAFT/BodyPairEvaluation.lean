import CurrentAFT.BackgroundAtomEvaluation

/-! Literal degree-two evaluation through the actual safe body channel. -/

namespace CurrentAFT.BodyPairEvaluation

open AFT ControlCoordinates ControlProduct LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation BodyChannelEvaluation
  PairCertificateFamilies DiffusePair DiffusePairBounds LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution DiffusePair.safePairProfile

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem pairBodyRaw_polynomial {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Body → Body → ℝ) :
    kernelPolynomial primary body primaryForms bodyForms (pairBodyRaw density) =
      densityPolynomial body bodyForms 2 (pairWordProfile density) := by
  simp only [kernelPolynomial, pairBodyRaw, densityPolynomial, pairWordProfile,
    Fin.prod_univ_zero, Fintype.sum_unique, one_mul]

theorem bodyPairFamily_generic_image {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForms color).IsHomogeneous 1) (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 2 ≤ order) (density : Body → Body → ℝ)
    (hfirst : ∀ second, ∑ first, body.weight first * density first second = 0)
    (hsecond : ∀ first, ∑ second, body.weight second * density first second = 0)
    (hsymmetric : ∀ first second, density first second = density second first) :
    familyHom primary body primaryForms bodyForms hprimary hbody order
      (Pi.single (bodyPairArity order horder) (bodyPairKernel primary body density hfirst hsecond)) =
        TruncatedOutput.quotientMap order (densityPolynomial body bodyForms 2 (pairWordProfile density)) := by
  change familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [familyLinear_single]
  change TruncatedOutput.quotientMap order (kernelPolynomial primary body primaryForms bodyForms
    (bodyPairKernel primary body density hfirst hsecond).val) = _
  rw [bodyPairKernel_val _ _ _ _ _ hsymmetric, pairBodyRaw_polynomial]

theorem diffuseBodyCertificate_image (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    evaluation security order (diffuseBodyCertificate security order horder scalar) =
      TruncatedOutput.quotientMap order (massPolynomial security 2
        (bodyTensorMass security 2 (pairWordProfile (bodyPairDensity security scalar)))) := by
  have h := bodyPairFamily_generic_image (primaryLaw security) (bodyReference security)
    (primaryForm security) (bodyForm security) (primaryForm_homogeneous security) (bodyForm_homogeneous security)
    order horder (bodyPairDensity security scalar) (bodyPairDensity_centered_first security scalar)
    (bodyPairDensity_centered_second security scalar) (bodyPairDensity_symmetric security scalar)
  rw [bodyTensor_polynomial] at h
  exact h

theorem bodyTensorMass_two (security : ℕ) (density : SafePalette security → SafePalette security → ℝ)
    (word : Fin 2 → ActualControls.Palette security) :
    bodyTensorMass security 2 (pairWordProfile density) word =
      MarkedPairLeading.bodyConvolution security (safeMass security (fun first =>
        MarkedPairLeading.bodyConvolution security (safeMass security (density first)) (word 1))) (word 0) := by
  have hresponse : TensorChannel.apply 2 (fun _ => bodyDensityChannel security)
      (pairWordProfile density) word = bodyDensityChannel security
        (fun first => bodyDensityChannel security (density first) (word 1)) (word 0) := rfl
  have hinside : (fun first => bodyDensityChannel security (density first) (word 1)) =
      ((primaryLaw security).weight (word 1))⁻¹ • (fun first =>
        MarkedPairLeading.bodyConvolution security (safeMass security (density first)) (word 1)) := by
    funext first
    simp only [bodyDensityChannel_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [bodyTensorMass, hresponse, referenceWeight, Fin.prod_univ_two, hinside,
    map_smul, Pi.smul_apply, smul_eq_mul, bodyDensityChannel_apply]
  field_simp [(primaryReference_positive security (word 0)).ne', (primaryReference_positive security (word 1)).ne']

theorem weightedEmbedding_subtype {State : Type*} [Fintype State] (law : FiniteDist State)
    (safe : State → Prop) (hzero : ∀ state, ¬safe state → law.weight state = 0)
    (density : {state // safe state} → ℝ) (output : State) :
    weightedEmbedding (supportedLaw law safe hzero) Subtype.val density output =
      if h : safe output then law.weight output * density ⟨output, h⟩ else 0 := by
  let extension : State → ℝ := fun state => if h : safe state then density ⟨state, h⟩ else 0
  have hext : (fun point : {state // safe state} => extension point.val) = density := by
    funext point
    exact dif_pos point.property
  have h := congrFun (weightedEmbedding_supported law safe hzero extension) output
  rw [hext] at h
  rw [h]
  by_cases hs : safe output
  · simp only [extension, dif_pos hs]
  · simp only [extension, dif_neg hs, mul_zero]

theorem safeMass_apply (security : ℕ) (density : SafePalette security → ℝ) (output : ActualControls.Palette security) :
    safeMass security density output = if h : InwardAnchor.SafeColor security output then
      (centerLaw security).weight output * density ⟨output, h⟩ else 0 := by
  unfold safeMass bodyReference
  exact weightedEmbedding_subtype _ _ _ density output

theorem safeMass_pairRow (security : ℕ) (scalar : ℤ) (first : SafePalette security) :
    safeMass security (bodyPairDensity security scalar first) =
      ((bodyReference security).weight first)⁻¹ • safePairProfile security scalar first.val := by
  funext second
  rw [safeMass_apply]
  by_cases hs : InwardAnchor.SafeColor security second
  · rw [dif_pos hs]
    have h := bodyPairDensity_profile security scalar first ⟨second, hs⟩
    have hw : (bodyReference security).weight ⟨second, hs⟩ = (centerLaw security).weight second := by
      unfold bodyReference
      rfl
    rw [hw] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [(bodyReference_positive security first).ne']
    nlinarith [h]
  · rw [dif_neg hs]
    simp only [Pi.smul_apply, smul_eq_mul,
      safePairProfile_zero_outside security scalar first.val second (Or.inr hs), mul_zero]

theorem safeMass_pairConvolution (security : ℕ) (scalar : ℤ) (second : ActualControls.Palette security) :
    safeMass security (fun first => MarkedPairLeading.bodyConvolution security
      (safeMass security (bodyPairDensity security scalar first)) second) =
      fun first => MarkedPairLeading.bodyConvolution security (safePairProfile security scalar first) second := by
  funext first
  rw [safeMass_apply]
  by_cases hs : InwardAnchor.SafeColor security first
  · rw [dif_pos hs, safeMass_pairRow, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hw : (bodyReference security).weight ⟨first, hs⟩ = (centerLaw security).weight first := by
      unfold bodyReference
      rfl
    rw [← hw]
    field_simp [(bodyReference_positive security ⟨first, hs⟩).ne']
  · rw [dif_neg hs]
    have hrow : safePairProfile security scalar first = 0 := by
      funext color
      exact safePairProfile_zero_outside security scalar first color (Or.inl hs)
    rw [hrow, map_zero, Pi.zero_apply]

theorem actual_bodyPair_tensor (security : ℕ) (scalar : ℤ) (word : Fin 2 → ActualControls.Palette security) :
    bodyTensorMass security 2 (pairWordProfile (bodyPairDensity security scalar)) word =
      MarkedPairLeading.bodyConvolution security (fun first =>
        MarkedPairLeading.bodyConvolution security (safePairProfile security scalar first) (word 1)) (word 0) := by
  rw [bodyTensorMass_two, safeMass_pairConvolution]

end

end CurrentAFT.BodyPairEvaluation

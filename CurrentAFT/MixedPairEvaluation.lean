import CurrentAFT.BodyPairEvaluation

/-! Exact evaluation of the marked mixed primary/body certificate. -/

namespace CurrentAFT.MixedPairEvaluation

open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundEvaluation BodyChannelEvaluation BodyPairEvaluation
  MarkedPairCertificates MarkedPairLeading MarkedPairSeed LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution MarkedPairSeed.seedDensity

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem densityPolynomial_one {Color Variable : Type*} [Fintype Color] (law : FiniteDist Color)
    (forms : Color → MvPolynomial Variable ℝ) (density : Color → ℝ) :
    densityPolynomial law forms 1 (oneWordProfile density) =
      ∑ point, MvPolynomial.C (law.weight point * density point) * forms point := by
  unfold densityPolynomial oneWordProfile
  simp only [Fin.prod_univ_one]
  exact ((Equiv.funUnique (Fin 1) Color).symm.sum_comp
    (fun word : Fin 1 → Color => MvPolynomial.C (law.weight (word 0) * density (word 0)) * forms (word 0))).symm

theorem rectangular_sum {Input Output : Type*} [Fintype Input] [Fintype Output]
    (input : FiniteDist Input) (output : FiniteDist Output) (hpositive : ∀ point, input.weight point ≠ 0)
    (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (density : Input → ℝ) :
    (∑ point, MvPolynomial.C (input.weight point * density point) *
      rectangularForm input.weight output.weight channel point) =
        RepresentedPolynomial.profileForm (fun point => output.weight point * channel density point) := by
  have h := rectangular_tensor_adjoint input output hpositive channel 1 (oneWordProfile density)
  have hchannel : TensorChannel.apply 1 (fun _ => channel) (oneWordProfile density) = oneWordProfile (channel density) := rfl
  rw [hchannel, densityPolynomial_one, densityPolynomial_one] at h
  exact h

def mixedPolynomial {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Primary → Body → ℝ) : MvPolynomial Variable ℝ :=
  ∑ color, ∑ center, MvPolynomial.C (primary.weight color * body.weight center * density color center) *
    primaryForms color * bodyForms center

theorem mixedKernel_polynomial {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Primary → Body → ℝ)
    (hprimary : ∀ center, primary.expectation (fun color => density color center) = 0)
    (hbody : ∀ color, body.expectation (density color) = 0) :
    kernelPolynomial primary body primaryForms bodyForms (mixedKernel primary body density hprimary hbody).val =
      mixedPolynomial primary body primaryForms bodyForms density := by
  unfold kernelPolynomial mixedKernel mixedPolynomial
  simp only [Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) Primary).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  apply Finset.sum_congr rfl
  intro color _
  calc
    _ = ∑ center, MvPolynomial.C (primary.weight color * body.weight center * density color center) *
        (primaryForms color * bodyForms center) := by
      simpa only [Equiv.funUnique_symm_apply, uniqueElim_const] using
        ((Equiv.funUnique (Fin 1) Body).symm.sum_comp (fun centers : Fin 1 → Body =>
          MvPolynomial.C (primary.weight color * body.weight (centers 0) * density color (centers 0)) *
            (primaryForms color * bodyForms (centers 0)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro center _
      ring

theorem mixed_primary_adjoint {Primary Body Output : Type*}
    [Fintype Primary] [Fintype Body] [Fintype Output]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (output : FiniteDist Output)
    (hpositive : ∀ point, primary.weight point ≠ 0)
    (channel : (Primary → ℝ) →ₗ[ℝ] (Output → ℝ)) (bodyForms : Body → MvPolynomial Output ℝ)
    (density : Primary → Body → ℝ) :
    mixedPolynomial primary body (rectangularForm primary.weight output.weight channel) bodyForms density =
      ∑ value, MvPolynomial.C (output.weight value) * MvPolynomial.X value *
        (∑ center, MvPolynomial.C (body.weight center * channel (fun color => density color center) value) * bodyForms center) := by
  have hgroup : mixedPolynomial primary body (rectangularForm primary.weight output.weight channel) bodyForms density =
      ∑ center, MvPolynomial.C (body.weight center) * bodyForms center *
        (∑ color, MvPolynomial.C (primary.weight color * density color center) *
          rectangularForm primary.weight output.weight channel color) := by
    unfold mixedPolynomial
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro center _
    apply Finset.sum_congr rfl
    intro color _
    ring
  rw [hgroup]
  simp_rw [rectangular_sum primary output hpositive channel]
  simp only [RepresentedPolynomial.profileForm_apply, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  apply Finset.sum_congr rfl
  intro center _
  ring

theorem body_sum (security : ℕ) (density : SafePalette security → ℝ) :
    (∑ point, MvPolynomial.C ((bodyReference security).weight point * density point) * bodyForm security point) =
      RepresentedPolynomial.profileForm (bodyConvolution security (safeMass security density)) := by
  simp_rw [bodyForm_rectangular]
  rw [rectangular_sum _ _ (fun point => (bodyReference_positive security point).ne')]
  congr 1
  funext output
  rw [bodyDensityChannel_apply]
  field_simp [(primaryReference_positive security output).ne']

theorem mixed_actual_polynomial (security : ℕ) (scalar : MarkedPairSeed.Scalar security) :
    mixedPolynomial (primaryLaw security) (bodyReference security) (primaryForm security) (bodyForm security)
      (inverseDensity security scalar) =
      ∑ primary, MvPolynomial.C ((primaryLaw security).weight primary) * MvPolynomial.X primary *
        RepresentedPolynomial.profileForm (bodyConvolution security (safeMass security (seedDensity security scalar primary))) := by
  have hforms : primaryForm security = rectangularForm (primaryLaw security).weight (primaryLaw security).weight
      (densityResponse security) := rfl
  rw [hforms, mixed_primary_adjoint _ _ _ (fun point => (primaryReference_positive security point).ne')]
  simp_rw [inverseDensity_primary_response, body_sum]

theorem safeMass_seedProfile (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : ActualControls.Palette security) :
    (primaryLaw security).weight primary • safeMass security (seedDensity security scalar primary) =
      MarkedPairLeading.seedProfile security scalar primary := by
  funext center
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [safeMass_apply]
  by_cases hs : InwardAnchor.SafeColor security center
  · rw [dif_pos hs]
    have hw : (bodyReference security).weight ⟨center, hs⟩ = (centerLaw security).weight center := by
      unfold bodyReference
      rfl
    rw [← hw, ← mul_assoc]
    exact seedDensity_profile security scalar primary ⟨center, hs⟩
  · rw [dif_neg hs, mul_zero, seedProfile_zero_outside security scalar primary center hs]

theorem massPolynomial_pair (security : ℕ) (profile : ActualControls.Palette security → ActualControls.Palette security → ℝ) :
    massPolynomial security 2 (pairWordProfile profile) =
      ∑ first, ∑ second, MvPolynomial.C (profile first second) * MvPolynomial.X first * MvPolynomial.X second := by
  unfold massPolynomial pairWordProfile
  simp only [Fin.prod_univ_two]
  calc
    _ = ∑ first, ∑ second, MvPolynomial.C (profile first second) * (MvPolynomial.X first * MvPolynomial.X second) := by
      simpa only [Fintype.sum_prod_type, finTwoArrowEquiv, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one] using
        ((finTwoArrowEquiv (ActualControls.Palette security)).symm.sum_comp
          (fun word : Fin 2 → ActualControls.Palette security =>
            MvPolynomial.C (profile (word 0) (word 1)) * (MvPolynomial.X (word 0) * MvPolynomial.X (word 1)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      ring

theorem markedMixed_polynomial (security : ℕ) (scalar : MarkedPairSeed.Scalar security) :
    mixedPolynomial (primaryLaw security) (bodyReference security) (primaryForm security) (bodyForm security)
      (inverseDensity security scalar) = massPolynomial security 2
        (pairWordProfile (fun primary output => bodyConvolution security (MarkedPairLeading.seedProfile security scalar primary) output)) := by
  rw [mixed_actual_polynomial, massPolynomial_pair]
  apply Finset.sum_congr rfl
  intro primary _
  have hprofile : RepresentedPolynomial.profileForm
      (bodyConvolution security (MarkedPairLeading.seedProfile security scalar primary)) =
      MvPolynomial.C ((primaryLaw security).weight primary) * RepresentedPolynomial.profileForm
        (bodyConvolution security (safeMass security (seedDensity security scalar primary))) := by
    rw [← safeMass_seedProfile security scalar primary, map_smul, map_smul, MvPolynomial.smul_eq_C_mul]
  have hsum : (∑ output, MvPolynomial.C (bodyConvolution security
      (MarkedPairLeading.seedProfile security scalar primary) output) * MvPolynomial.X primary * MvPolynomial.X output) =
      MvPolynomial.X primary * RepresentedPolynomial.profileForm
        (bodyConvolution security (MarkedPairLeading.seedProfile security scalar primary)) := by
    rw [RepresentedPolynomial.profileForm_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro output _
    ring
  rw [hsum, hprofile]
  ring

theorem mixedFamily_generic_image {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimaryForms : ∀ color, (primaryForms color).IsHomogeneous 1)
    (hbodyForms : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 2 ≤ order) (density : Primary → Body → ℝ)
    (hprimary : ∀ center, primary.expectation (fun color => density color center) = 0)
    (hbody : ∀ color, body.expectation (density color) = 0) :
    familyHom primary body primaryForms bodyForms hprimaryForms hbodyForms order
      (Pi.single (mixedArity order horder) (mixedKernel primary body density hprimary hbody)) =
        TruncatedOutput.quotientMap order (mixedPolynomial primary body primaryForms bodyForms density) := by
  change familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [familyLinear_single]
  change TruncatedOutput.quotientMap order (kernelPolynomial primary body primaryForms bodyForms
    (mixedKernel primary body density hprimary hbody).val) = _
  rw [mixedKernel_polynomial]

theorem markedMixedCertificate_image (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    BackgroundEvaluation.evaluation security order (markedMixedCertificate security order horder scalar) =
      TruncatedOutput.quotientMap order (massPolynomial security 2 (pairWordProfile
        (fun primary output => bodyConvolution security (MarkedPairLeading.seedProfile security scalar primary) output))) := by
  have h := mixedFamily_generic_image (primaryLaw security) (bodyReference security)
    (primaryForm security) (bodyForm security) (primaryForm_homogeneous security) (bodyForm_homogeneous security)
    order horder (inverseDensity security scalar) (inverseDensity_centered_primary security scalar)
    (inverseDensity_centered_body security scalar)
  rw [markedMixed_polynomial] at h
  exact h

end

end CurrentAFT.MixedPairEvaluation

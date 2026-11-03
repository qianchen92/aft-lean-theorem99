import CurrentAFT.BodyPairEvaluation

/-! The actual protected diffuse pair has exactly its constructed certificate. -/

namespace CurrentAFT.DiffusePairEvaluation

open AFT AFT.SafeConvolution AFT.SafePair ControlCoordinates LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies PairReindex PairSmoothing
  BackgroundEvaluation BodyChannelEvaluation BodyPairEvaluation DiffusePair DiffusePairBounds FringeCertificate
  DiffusePairResidual DiffusePairResidualRates DiffusePairCertificates LocalCoefficientFamily
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution DiffusePair.safePairProfile DiffusePairResidual.seedProfile
  DiffusePairResidual.rootResiduePairLaw BodyChannelEvaluation.bodyTensorMass DiffusePairBounds.bodyPairDensity

noncomputable def cyclicEquiv (modulus : ℕ) [NeZero modulus] (shift : ZMod modulus) : Fin modulus ≃ Fin modulus :=
  (ZMod.finEquiv modulus).toEquiv.trans ((Equiv.addRight shift).trans (ZMod.finEquiv modulus).toEquiv.symm)

theorem cyclic_symm (modulus : ℕ) [NeZero modulus] (shift : ZMod modulus) (color : Fin modulus) :
    (cyclicEquiv modulus shift).symm color =
        (ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) color - shift) := by
  cases modulus with
  | zero => exact Fin.elim0 color
  | succ modulus =>
      simp [cyclicEquiv, ZMod.finEquiv, Equiv.symm_trans_apply, Equiv.addRight_symm,
        Equiv.coe_addRight, sub_eq_add_neg]
      rfl

theorem finite_pair_convolution (modulus : ℕ) [NeZero modulus]
    {Seed : Type*} [Fintype Seed] (law : FiniteDist Seed) (shift : Seed → ZMod modulus)
    (profile : Fin modulus → Fin modulus → ℝ) (first second : Fin modulus) :
    (∑ left, law.weight left * ∑ right, law.weight right *
      profile ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) first - shift left))
        ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) second - shift right))) =
      convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight
        (fun color => liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2)
        ((ZMod.finEquiv modulus) first, (ZMod.finEquiv modulus) second) := by
  change _ = ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).expectation
    (fun displacement => liftPair (ZMod.finEquiv modulus).toEquiv profile
      ((ZMod.finEquiv modulus) first - displacement.1) ((ZMod.finEquiv modulus) second - displacement.2))
  rw [FiniteDist.expectation_map, FiniteDist.expectation_prod]
  rfl

theorem cyclic_pair_convolution (modulus : ℕ) [NeZero modulus]
    {Seed : Type*} [Fintype Seed] (law : FiniteDist Seed) (shift : Seed → ZMod modulus)
    (profile : Fin modulus → Fin modulus → ℝ) (first second : Fin modulus) :
    (∑ left, law.weight left * ∑ right, law.weight right *
      profile ((cyclicEquiv modulus (shift left)).symm first)
        ((cyclicEquiv modulus (shift right)).symm second)) =
      convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight
        (fun color => liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2)
        ((ZMod.finEquiv modulus) first, (ZMod.finEquiv modulus) second) := by
  simp only [cyclic_symm]
  exact finite_pair_convolution modulus law shift profile first second

theorem body_pair_convolution (security : ℕ) (scalar : ℤ) (first second : ActualControls.Palette security) :
    MarkedPairLeading.bodyConvolution security (fun left =>
      MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first =
      pullbackPair (Parameters.modulus security)
        (convolution (rootResiduePairLaw security).weight (seedProfile security scalar)) first second := by
  unfold MarkedPairLeading.bodyConvolution BackgroundCertificates.rootConvolutionProfile
  unfold pullbackPair rootResiduePairLaw rootPairLaw rootPairShift seedProfile
  simp only [LinearMap.coe_mk, AddHom.coe_mk, shiftEquiv]
  change (∑ left, (actualSeedLaw security).weight left * ∑ right, (actualSeedLaw security).weight right *
    safePairProfile security scalar
      ((cyclicEquiv (Parameters.modulus security) (actualBlur security left)).symm first)
      ((cyclicEquiv (Parameters.modulus security) (actualBlur security right)).symm second)) = _
  exact cyclic_pair_convolution (Parameters.modulus security) (actualSeedLaw security)
    (fun seed => (actualBlur security seed : ZMod (Parameters.modulus security)))
    (safePairProfile security scalar) first second

theorem actual_bodyPair_convolution (security : ℕ) (scalar : ℤ) :
    bodyTensorMass security 2 (pairWordProfile (bodyPairDensity security scalar)) =
      pairWordProfile (pullbackPair (Parameters.modulus security)
        (convolution (rootResiduePairLaw security).weight (seedProfile security scalar))) := by
  funext word
  exact (actual_bodyPair_tensor security scalar word).trans
    (body_pair_convolution security scalar (word 0) (word 1))

theorem massPolynomial_add (security degree : ℕ)
    (first second : (Fin degree → ActualControls.Palette security) → ℝ) :
    massPolynomial security degree (first + second) =
      massPolynomial security degree first + massPolynomial security degree second := by
  unfold massPolynomial
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem pair_pullback_leading (modulus : ℕ) [NeZero modulus]
    (profile : Fin modulus → Fin modulus → ℝ) :
    pullbackPair modulus (uniformCanonical (fun color =>
      liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2)) =
        canonicalPair (fun _ => 1 / (modulus : ℝ)) profile := by
  have h := canonicalPair_uniform_lift (ZMod.finEquiv modulus).toEquiv profile
  simp only [ZMod.card, Fintype.card_fin] at h
  funext first second
  change canonicalPair (fun _ => 1 / (Fintype.card (ZMod modulus) : ℝ))
      (liftPair (ZMod.finEquiv modulus).toEquiv profile)
      ((ZMod.finEquiv modulus) first) ((ZMod.finEquiv modulus) second) = _
  simp only [ZMod.card]
  rw [h]
  simp only [liftPair]
  cases modulus with
  | zero => exact Fin.elim0 first
  | succ modulus => rfl

theorem diffuseCertificate_image (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    evaluation security order (diffuseCertificate security order horder scalar) =
      TruncatedOutput.quotientMap order (massPolynomial security 2
        (pairWordProfile (canonicalPair (uniformProfile security) (pairProfile security scalar)))) := by
  unfold diffuseCertificate
  rw [map_add, diffuseBodyCertificate_image, diffusePrimary_image,
    actual_bodyPair_convolution, ← map_add, ← massPolynomial_add]
  congr 2
  funext word
  change pullbackPair (Parameters.modulus security)
      (convolution (rootResiduePairLaw security).weight (seedProfile security scalar)) (word 0) (word 1) +
      pullbackPair (Parameters.modulus security) (residualProfile security scalar) (word 0) (word 1) = _
  rw [← pullbackPair_add, residualProfile_leading]
  simpa only [originalProfile, pairWordProfile, uniformProfile, one_div] using
    congrFun (congrFun (pair_pullback_leading (Parameters.modulus security) (pairProfile security scalar)) (word 0)) (word 1)

end

end CurrentAFT.DiffusePairEvaluation

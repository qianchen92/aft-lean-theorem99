import CurrentAFT.RationalDiffuseCertificateProgram
import CurrentAFT.RationalMassLiftTensorProgram
import CurrentAFT.DiffusePairCertificates
import CurrentAFT.RationalFamilyProductProgram

/-! # Both original coefficient fibers of the actual diffuse certificate -/
namespace CurrentAFT.RationalDiffuseFamilyProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalDiffuseResidualProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def bodyTable {Scalar Primary Body : Type*} [Zero Scalar] (order : ℕ) (value : Body → Body → Scalar) :
    Table Scalar Primary Body order := fun arity _ centers =>
  if h : arity.val.1.val = 0 ∧ arity.val.2.val = 2 then
    value (centers ⟨0, by omega⟩) (centers ⟨1, by omega⟩) else 0

def primaryTable {Scalar Primary Body : Type*} [Zero Scalar] (order degree : ℕ)
    (value : (Fin degree → Primary) → Scalar) : Table Scalar Primary Body order := fun arity colors _ =>
  if h : degree = arity.val.1.val ∧ 0 = arity.val.2.val then value (colors ∘ finCongr h.1) else 0

def body (security bits order : ℕ) (scalar : ℤ) : Table ℚ ℕ ℕ order :=
  bodyTable order (bodyDensity security bits scalar)

def primary (security bits order : ℕ) (scalar : ℤ) : Table ℚ ℕ ℕ order :=
  primaryTable order 2 (RationalMassLiftTensorProgram.current security bits 2
    (fun word => residual security bits scalar (word 0) (word 1)))

def current (security bits order : ℕ) (scalar : ℤ) : Table ℚ ℕ ℕ order :=
  body security bits order scalar + primary security bits order scalar

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff Parameters.safeMargin
  primaryLaw centerLaw PublicParameterProgram.modulus

theorem primaryTable_data (security order degree : ℕ) (hdegree : degree ≤ order)
    (profile : (Fin degree → Palette security) → ℝ) (hcentered : PrimaryTensorInverse.MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    primaryTable order degree (PrimaryTensorInverse.massLift security degree profile) =
      fun arity => (PrimaryMassFamilies.massCertificateFamily security order degree hdegree profile hcentered hsymmetric arity).val := by
  funext arity colors centers
  by_cases h : arity = PrimaryMassFamilies.primaryArity order degree hdegree
  · subst arity
    simp only [PrimaryMassFamilies.massCertificateFamily, Pi.single_eq_same]
    simp [primaryTable, PrimaryMassFamilies.primaryArity, PrimaryMassFamilies.massLiftKernel]
  · have hshape : ¬(degree = arity.val.1.val ∧ 0 = arity.val.2.val) := by
      rintro ⟨hfirst, hsecond⟩
      apply h
      apply Subtype.ext
      exact Prod.ext (Fin.ext hfirst.symm) (Fin.ext hsecond.symm)
    simp only [primaryTable, dif_neg hshape, PrimaryMassFamilies.massCertificateFamily,
      Pi.single_eq_of_ne h, Submodule.coe_zero, Pi.zero_apply]

theorem body_data (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    bodyTable order (DiffusePairBounds.bodyPairDensity security scalar) =
      fun arity => (PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val := by
  funext arity colors centers
  by_cases h : arity = PairCertificateFamilies.bodyPairArity order horder
  · subst arity
    simp only [PairCertificateFamilies.diffuseBodyCertificate, Pi.single_eq_same]
    rw [PairCertificateFamilies.bodyPairKernel_val _ _ _ _ _ (DiffusePairBounds.bodyPairDensity_symmetric security scalar)]
    rfl
  · have hshape : ¬(arity.val.1.val = 0 ∧ arity.val.2.val = 2) := by
      rintro ⟨hfirst, hsecond⟩
      apply h
      apply Subtype.ext
      exact Prod.ext (Fin.ext hfirst) (Fin.ext hsecond)
    simp only [bodyTable, dif_neg hshape, PairCertificateFamilies.diffuseBodyCertificate,
      Pi.single_eq_of_ne h, Submodule.coe_zero, Pi.zero_apply]

def primaryErrorConstant (security : ℕ) : ℝ :=
  RationalMassLiftTensorProgram.errorConstant security 2
    (2 * pairBound security) (10 * pairBound security)

theorem residual_bound (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(residual security bits scalar first.val second.val : ℝ)| ≤ 2 * pairBound security := by
  rw [RationalDiffuseResidualProgram.residual, Rat.cast_sub]
  have hq : 1 ≤ (Parameters.modulus security : ℝ) := by exact_mod_cast (Parameters.modulus_spec security).2.pos
  have hu : |(uniformCanonical security bits scalar first.val second.val : ℝ)| ≤ pairBound security := by
    rw [uniformCanonical_cast]
    have href (color : Palette security) : |(1 : ℝ) / Parameters.modulus security| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq
    simpa only [Fintype.card_fin, pairBound, mul_one] using
      canonicalPair_bound _ _ 1 (by norm_num) href (pair_bound security bits scalar) first second
  exact (abs_sub _ _).trans ((add_le_add hu (smoothedSeed_bound security bits scalar first second)).trans_eq (by ring))

theorem primary_coefficient_error (security bits : ℕ) (scalar : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (word : Fin 2 → Palette security) :
    |(RationalMassLiftTensorProgram.current security bits 2
      (fun source => residual security bits scalar (source 0) (source 1)) (fun index => (word index).val) : ℝ) -
      PrimaryTensorInverse.massLift security 2 (DiffusePairCertificates.residualMass security scalar) word| ≤
      primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
  exact RationalMassLiftTensorProgram.current_error security bits 2 _ _
    (2 * pairBound security) (10 * pairBound security) (by unfold pairBound; positivity) (by unfold pairBound; positivity)
    (fun source => residual_bound security bits scalar (source 0) (source 1))
    (fun source => residual_error security bits scalar (source 0) (source 1)) hfirst hprecision hbudget word

def errorConstant (security : ℕ) : ℝ :=
  RationalDiffuseCertificateProgram.bodyErrorConstant security + primaryErrorConstant security

theorem errorConstant_nonneg (security : ℕ) : 0 ≤ errorConstant security := by
  have hm := RationalMassLiftProgram.errorConstant_nonneg security
  have hf := RationalMassLiftTensorProgram.factorBound_one_le security
  unfold errorConstant RationalDiffuseCertificateProgram.bodyErrorConstant primaryErrorConstant
    RationalMassLiftTensorProgram.errorConstant pairBound RationalBackgroundDensities.centerErrorConstant
  positivity

theorem current_error (security bits order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (DiffusePairCertificates.diffuseCertificate security order horder scalar arity).val colors centers| ≤
      errorConstant security * (1 / (2 : ℝ)^bits) := by
  have hb : |(body security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val colors centers| ≤
      RationalDiffuseCertificateProgram.bodyErrorConstant security * (1 / (2 : ℝ)^bits) := by
    rw [← congrFun (congrFun (congrFun (body_data security order horder scalar) arity) colors) centers]
    unfold body bodyTable
    split_ifs
    · exact RationalDiffuseCertificateProgram.bodyDensity_error security bits scalar _ _ hprecision hbudget
    · simp only [Rat.cast_zero, sub_self, abs_zero]
      unfold RationalDiffuseCertificateProgram.bodyErrorConstant pairBound RationalBackgroundDensities.centerErrorConstant
      positivity
  have hp : |(primary security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar arity).val colors centers| ≤
      primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
    unfold DiffusePairCertificates.diffusePrimaryCertificate
    rw [← congrFun (congrFun (congrFun (primaryTable_data security order 2 horder
      (DiffusePairCertificates.residualMass security scalar) (DiffusePairCertificates.residualMass_centered security scalar)
      (DiffusePairCertificates.residualMass_symmetric security scalar)) arity) colors) centers]
    unfold primary primaryTable
    split_ifs
    · exact primary_coefficient_error security bits scalar hfirst hprecision hbudget _
    · simp only [Rat.cast_zero, sub_self, abs_zero]
      unfold primaryErrorConstant RationalMassLiftTensorProgram.errorConstant RationalMassLiftTensorProgram.factorBound
        RationalMassLiftProgram.errorConstant RationalTensorInverseProgram.actualBound RationalDensityInverseProgram.inverseBound
        RationalFirstResponseProgram.inverseErrorConstant pairBound
      positivity
  change |((body security bits order scalar arity _ _ + primary security bits order scalar arity _ _ : ℚ) : ℝ) -
    ((PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val colors centers +
      (DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar arity).val colors centers)| ≤ _
  rw [Rat.cast_add]
  have hsplit : (body security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) +
      (primary security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      ((PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val colors centers +
        (DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar arity).val colors centers) =
    ((body security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (PairCertificateFamilies.diffuseBodyCertificate security order horder scalar arity).val colors centers) +
    ((primary security bits order scalar arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar arity).val colors centers) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hb hp).trans_eq (by unfold errorConstant; ring))

end
end CurrentAFT.RationalDiffuseFamilyProgram

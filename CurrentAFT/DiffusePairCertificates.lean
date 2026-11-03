import CurrentAFT.DiffusePairResidualRates
import CurrentAFT.PairCertificateFamilies
import CurrentAFT.PrimaryMassFamilies

/-! Complete actual diffuse quadratic certificate: two safe body slots and a small two-primary residual. -/

namespace CurrentAFT.DiffusePairCertificates

open AFT AFT.SafeConvolution ControlCoordinates GradedControlAlgebra GradedControlNorm
  GradedControlStability DiffuseProfiles ProposalPrimary ActualControls BackgroundRates
  BackgroundFamilies PairCertificateFamilies PrimaryTensorInverse PrimaryMassFamilies
  DiffusePair DiffusePairResidual DiffusePairResidualRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor DiffusePairResidualRates.finiteResidual
  DiffusePairResidual.seedProfile DiffusePairResidual.originalProfile DiffusePairResidual.rootResiduePairLaw
  PrimaryTensorInverse.massLeading

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def residualMass (security : ℕ) (scalar : ℤ) (word : Fin 2 → ActualControls.Palette security) : ℝ :=
  pairWordProfile (finiteResidual security scalar) word

theorem residualMass_centered (security : ℕ) (scalar : ℤ) : MassCentered 2 (residualMass security scalar) := by
  intro index word
  fin_cases index
  · simpa [residualMass, pairWordProfile, Function.update_apply] using (finiteResidual_canonical security scalar).2 (word 1)
  · simpa [residualMass, pairWordProfile, Function.update_apply] using (finiteResidual_canonical security scalar).1 (word 0)

theorem residualMass_symmetric (security : ℕ) (scalar : ℤ)
    (permutation : Equiv.Perm (Fin 2)) (word : Fin 2 → ActualControls.Palette security) :
    residualMass security scalar (word ∘ permutation) = residualMass security scalar word := by
  exact pairWordProfile_symmetric (finiteResidual security scalar)
    (finiteResidual_symmetric security scalar) permutation word

theorem residualMass_energy (security : ℕ) (scalar : ℤ) :
    massEnergy security 2 (residualMass security scalar) =
      BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight (finiteResidual security scalar) := by
  exact pairWordProfile_energy (primaryLaw security).weight (finiteResidual security scalar)

def diffusePrimaryCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) : ActualFamily security order :=
  massCertificateFamily security order 2 horder (residualMass security scalar)
    (residualMass_centered security scalar) (residualMass_symmetric security scalar)

theorem diffusePrimaryCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (diffusePrimaryCertificate security order horder scalar) ≤
        387456 / (Parameters.base security : ℝ) ^ 141 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hfactor : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> ring
  have hnorm := massCertificateFamily_norm security order 2 horder
    (primaryFactor security) (bodyFactor security) hfactor (residualMass security scalar)
    (residualMass_centered security scalar) (residualMass_symmetric security scalar)
  have hinput : Real.sqrt (massEnergy security 2 (residualMass security scalar)) ≤
      6054 / (Parameters.base security : ℝ) ^ 15 := by
    rw [residualMass_energy]
    exact finiteResidual_primary_norm_decay security scalar hscalar
  calc
    _ ≤ primaryFactor security ^ 2 * (2 / activation security) ^ 2 *
        Real.sqrt (massEnergy security 2 (residualMass security scalar)) := hnorm
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) ^ 2 * (8 * (Parameters.base security : ℝ)) ^ 2 *
        (6054 / (Parameters.base security : ℝ) ^ 15) := by
      rw [primaryFactor_eq]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv 2) (sq_nonneg _))
        hinput (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

def diffuseCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) : ActualFamily security order :=
  diffuseBodyCertificate security order horder scalar + diffusePrimaryCertificate security order horder scalar

theorem diffuseCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (diffuseCertificate security order horder scalar) ≤
        388480 / (Parameters.base security : ℝ) ^ 141 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  calc
    _ ≤ familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (diffuseBodyCertificate security order horder scalar) +
        familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (diffusePrimaryCertificate security order horder scalar) := familyNorm_add_le _ _ _ _ _ hp hbdy _ _
    _ ≤ 1024 / (Parameters.base security : ℝ) ^ 150 + 387456 / (Parameters.base security : ℝ) ^ 141 :=
      add_le_add (diffuseBodyCertificate_norm_decay security order horder scalar hscalar)
        (diffusePrimaryCertificate_norm security order horder scalar hscalar)
    _ ≤ 1024 / (Parameters.base security : ℝ) ^ 141 + 387456 / (Parameters.base security : ℝ) ^ 141 :=
      add_le_add (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega))) le_rfl
    _ = _ := by ring

theorem diffuseCertificate_population_bound (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (Parameters.legCount security : ℝ) *
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (diffuseCertificate security order horder scalar) ≤
          388480 / (Parameters.base security : ℝ) ^ 13 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (388480 / (Parameters.base security : ℝ) ^ 141) :=
      mul_le_mul_of_nonneg_left (diffuseCertificate_norm security order horder scalar hscalar) (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp

theorem diffusePrimaryCertificate_leading (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    massLeading security 2 (fun colors => ((diffusePrimaryCertificate security order horder scalar)
      (PrimaryMassFamilies.primaryArity order 2 horder)).val colors Fin.elim0) = residualMass security scalar :=
  massCertificateFamily_leading security order 2 horder (residualMass security scalar)
    (residualMass_centered security scalar) (residualMass_symmetric security scalar)

theorem diffuse_body_residual_decomposition (security : ℕ) (scalar : ℤ) :
    convolution (rootResiduePairLaw security).weight (seedProfile security scalar) +
      residualProfile security scalar = uniformCanonical (originalProfile security scalar) :=
  residualProfile_leading security scalar

end

end CurrentAFT.DiffusePairCertificates

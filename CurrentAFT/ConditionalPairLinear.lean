import CurrentAFT.ConditionalPairMean
import CurrentAFT.PrimaryMassFamilies
import CurrentAFT.BackgroundLinear

/-!
# Actual conditional pair-linear coefficients and their population budget

The coefficient is obtained by the actual primary tensor inverse from the
fixed-scalar mean. The scalar is retained through the later multiplication
with the attachment factor.
-/

namespace CurrentAFT.ConditionalPairLinear

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse
  ConditionalPairMean PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundRates BackgroundLinear
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth ProposalPrimary.primaryLaw
  ProposalPrimary.centerLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def wordMean (security : ℕ) (scalar : ConditionalPairMean.Scalar security)
    (word : Fin 1 → ActualControls.Palette security) : ℝ := centeredMean security scalar (word 0)

theorem wordMean_centered (security : ℕ) (scalar : ConditionalPairMean.Scalar security) :
    MassCentered 1 (wordMean security scalar) := by
  intro index word
  have hindex : index = 0 := Subsingleton.elim _ _
  subst index
  simpa only [wordMean, Function.update_self] using centeredMean_mass security scalar

theorem wordMean_symmetric (security : ℕ) (scalar : ConditionalPairMean.Scalar security)
    (permutation : Equiv.Perm (Fin 1)) (word : Fin 1 → ActualControls.Palette security) :
    wordMean security scalar (word ∘ permutation) = wordMean security scalar word := by
  have hindex : permutation 0 = 0 := Subsingleton.elim _ _
  simp only [wordMean, Function.comp_apply, hindex]

def certificate (security order : ℕ) (horder : 1 ≤ order)
    (scalar : ConditionalPairMean.Scalar security) : ActualFamily security order :=
  massCertificateFamily security order 1 horder (wordMean security scalar)
    (wordMean_centered security scalar) (wordMean_symmetric security scalar)

private theorem oneWord_energy {Color : Type*} [Fintype Color]
    (reference profile : Color → ℝ) :
    (∑ word : Fin 1 → Color, profile (word 0) ^ 2 / (∏ index, reference (word index))) =
      profileSquareNorm reference profile := by
  rw [← (Equiv.funUnique (Fin 1) Color).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, pow_one, profileSquareNorm]

theorem wordMean_energy (security : ℕ) (scalar : ConditionalPairMean.Scalar security) :
    massEnergy security 1 (wordMean security scalar) =
      profileSquareNorm (primaryLaw security).weight (centeredMean security scalar) := by
  exact oneWord_energy (primaryLaw security).weight (centeredMean security scalar)

theorem modulus_anchor_ratio (security : ℕ) :
    (Parameters.modulus security : ℝ) / Parameters.anchorWidth security ≤
      131072 * (Parameters.base security : ℝ) ^ 16 := by
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hanchor : (Parameters.anchorWidth security : ℝ) = (Parameters.base security : ℝ) ^ 48 := by
    simp only [Parameters.anchorWidth, Parameters.scale, ← pow_mul, Nat.cast_pow]
  rw [hanchor]
  apply (div_le_iff₀ (pow_pos (base_pos security) _)).mpr
  simpa only [mul_assoc, ← pow_add] using hq

theorem wordMean_norm (security : ℕ) (scalar : ConditionalPairMean.Scalar security) :
    Real.sqrt (massEnergy security 1 (wordMean security scalar)) ≤
      4096 * (Parameters.base security : ℝ) ^ 8 := by
  rw [wordMean_energy]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h := centeredMean_energy security scalar
  have hratio := modulus_anchor_ratio security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hpower : (1 : ℝ) ≤ (Parameters.base security : ℝ) ^ 16 := one_le_pow₀ hb1
  have hidentity : (4096 * (Parameters.base security : ℝ) ^ 8) ^ 2 =
      16777216 * (Parameters.base security : ℝ) ^ 16 := by ring
  rw [hidentity]
  simp only [div_eq_mul_inv, mul_assoc] at h hratio
  nlinarith

theorem certificate_norm (security order : ℕ) (horder : 1 ≤ order)
    (scalar : ConditionalPairMean.Scalar security) :
    certificateNorm security order (certificate security order horder scalar) ≤
      32768 / (Parameters.base security : ℝ) ^ 55 := by
  have hfactor : 0 ≤ primaryFactor security := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h := massCertificateFamily_norm security order 1 horder
    (primaryFactor security) (bodyFactor security) hfactor (wordMean security scalar)
    (wordMean_centered security scalar) (wordMean_symmetric security scalar)
  change certificateNorm security order (certificate security order horder scalar) ≤ _ at h
  simp only [pow_one] at h
  have hinverse : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have hh := activation_inverse_le security
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith
  calc
    _ ≤ primaryFactor security * (2 / activation security) *
        Real.sqrt (massEnergy security 1 (wordMean security scalar)) := h
    _ ≤ primaryFactor security * (8 * (Parameters.base security : ℝ)) *
        (4096 * (Parameters.base security : ℝ) ^ 8) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hinverse hfactor) (wordMean_norm security scalar)
        (Real.sqrt_nonneg _) (mul_nonneg hfactor (by positivity))
    _ = _ := by
      rw [primaryFactor_eq]
      field_simp [(base_pos security).ne']
      ring

theorem certificate_leading (security order : ℕ) (horder : 1 ≤ order)
    (scalar : ConditionalPairMean.Scalar security) :
    massLeading security 1 (fun colors =>
      ((certificate security order horder scalar)
        (PrimaryMassFamilies.primaryArity order 1 horder)).val colors Fin.elim0) =
      wordMean security scalar :=
  massCertificateFamily_leading security order 1 horder (wordMean security scalar)
    (wordMean_centered security scalar) (wordMean_symmetric security scalar)

theorem cross_population_budget (security order : ℕ) (horder : 1 ≤ order)
    (scalar : ConditionalPairMean.Scalar security) (queueShift : ℤ) :
    (Parameters.legCount security : ℝ) * certificateNorm security order
      (certificate security order horder scalar * translationCertificate security order horder queueShift) ≤
        1835008 / (Parameters.base security : ℝ) ^ 6 := by
  have hsub := GradedControlNorm.familyNorm_product_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security)
    (by unfold primaryFactor; positivity) (by unfold bodyFactor radius; positivity)
    (certificate security order horder scalar) (translationCertificate security order horder queueShift)
  have hnonneg : 0 ≤ certificateNorm security order (translationCertificate security order horder queueShift) :=
    certificateNorm_nonneg security order _
  have hbound := mul_le_mul (certificate_norm security order horder scalar)
    (translationCertificate_norm_decay security order horder queueShift) hnonneg (by positivity)
  have h := mul_le_mul_of_nonneg_left (hsub.trans hbound)
    (Nat.cast_nonneg (Parameters.legCount security) : (0 : ℝ) ≤ Parameters.legCount security)
  apply h.trans_eq
  rw [Parameters.legCount_eq, Nat.cast_pow]
  field_simp [(base_pos security).ne']
  ring

end

end CurrentAFT.ConditionalPairLinear

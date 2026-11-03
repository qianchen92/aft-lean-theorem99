import CurrentAFT.MarkedPairLeading
import CurrentAFT.PrimaryDeviationCertificate
import CurrentAFT.DiffusePairCertificates

/-! Complete fixed-scalar quadratic pair certificates in the actual family algebra. -/

namespace CurrentAFT.PairQuadraticFamilies

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability
  DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  MarkedPairCertificates PrimaryDeviationCertificate DiffusePairCertificates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def markedPairCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ActualFamily security order :=
  markedMixedCertificate security order horder scalar +
    familyProduct (primaryLaw security) (bodyReference security) order
      (certificate security order (by omega)) (freeCertificate security order (by omega))

theorem markedPairCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (markedPairCertificate security order horder scalar) ≤ 18400 / (Parameters.base security : ℝ) ^ 134 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have hprod := familyNorm_product_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) hp hbdy
    (certificate security order (by omega)) (freeCertificate security order (by omega))
  have hbound : familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (familyProduct (primaryLaw security) (bodyReference security) order
        (certificate security order (by omega)) (freeCertificate security order (by omega))) ≤
      (24 / (Parameters.base security : ℝ) ^ 63) * (84 / (Parameters.base security : ℝ) ^ 110) := by
    exact hprod.trans (mul_le_mul (certificate_norm security order (by omega))
      (freeCertificate_norm_decay security order (by omega))
      (familyNorm_nonneg _ _ _ _ _ hp hbdy _) (by positivity))
  calc
    _ ≤ familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (markedMixedCertificate security order horder scalar) +
        familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (familyProduct (primaryLaw security) (bodyReference security) order
            (certificate security order (by omega)) (freeCertificate security order (by omega))) :=
      familyNorm_add_le _ _ _ _ _ hp hbdy _ _
    _ ≤ 16384 / (Parameters.base security : ℝ) ^ 134 +
        (24 / (Parameters.base security : ℝ) ^ 63) * (84 / (Parameters.base security : ℝ) ^ 110) :=
      add_le_add (markedMixedCertificate_norm security order horder scalar) hbound
    _ = 16384 / (Parameters.base security : ℝ) ^ 134 + 2016 / (Parameters.base security : ℝ) ^ 173 := by ring
    _ ≤ 16384 / (Parameters.base security : ℝ) ^ 134 + 2016 / (Parameters.base security : ℝ) ^ 134 :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega)))
    _ = _ := by ring

def pairQuadraticCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ActualFamily security order :=
  (1 - activation security) • diffuseCertificate security order horder scalar.val +
    activation security • markedPairCertificate security order horder scalar

theorem pairQuadraticCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (pairQuadraticCertificate security order horder scalar) ≤ 406880 / (Parameters.base security : ℝ) ^ 134 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have ha := activation_pos security
  have haHalf := activation_le_half security
  have hdiff : familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (diffuseCertificate security order horder scalar.val) ≤ 388480 / (Parameters.base security : ℝ) ^ 134 := by
    exact (diffuseCertificate_norm security order horder scalar.val
      ((InwardAnchor.scalar_bound security scalar).trans (by omega))).trans
        (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega)))
  calc
    _ ≤ familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          ((1 - activation security) • diffuseCertificate security order horder scalar.val) +
        familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (activation security • markedPairCertificate security order horder scalar) :=
      familyNorm_add_le _ _ _ _ _ hp hbdy _ _
    _ = (1 - activation security) * familyNorm (primaryLaw security) (bodyReference security) order
          (primaryFactor security) (bodyFactor security) (diffuseCertificate security order horder scalar.val) +
        activation security * familyNorm (primaryLaw security) (bodyReference security) order
          (primaryFactor security) (bodyFactor security) (markedPairCertificate security order horder scalar) := by
      rw [familyNorm_smul, familyNorm_smul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security), abs_of_pos ha]
    _ ≤ 388480 / (Parameters.base security : ℝ) ^ 134 + 18400 / (Parameters.base security : ℝ) ^ 134 := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left hdiff (by linarith)).trans (by nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 388480) (pow_nonneg hb.le 134)])
      · exact (mul_le_mul_of_nonneg_left (markedPairCertificate_norm security order horder scalar) ha.le).trans
          (by nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 18400) (pow_nonneg hb.le 134)])
    _ = _ := by ring

theorem pairQuadraticCertificate_population_bound (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    (Parameters.legCount security : ℝ) *
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (pairQuadraticCertificate security order horder scalar) ≤ 406880 / (Parameters.base security : ℝ) ^ 6 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (406880 / (Parameters.base security : ℝ) ^ 134) :=
      mul_le_mul_of_nonneg_left (pairQuadraticCertificate_norm security order horder scalar) (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp

end

end CurrentAFT.PairQuadraticFamilies

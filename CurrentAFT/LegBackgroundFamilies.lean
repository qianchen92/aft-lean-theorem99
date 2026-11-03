import CurrentAFT.ActualPairBridge
import CurrentAFT.ConditionalPairLinear

/-!
# Complete same-scalar leg background families

The fixed leg scalar is shared by its off-body pair and attachment before
their coefficient products are formed. Only the complete quadratic and
cubic coefficients are averaged. The linear coefficient uses the exact
baseline-balanced recipe, preserving cancellation with the free population.
-/

namespace CurrentAFT.LegBackgroundFamilies

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability
  DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  BackgroundLinear PairQuadraticFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor BackgroundFamilies.freeCertificate
  BackgroundFamilies.translationCertificate BackgroundLinear.legLinearCertificate
  PairQuadraticFamilies.pairQuadraticCertificate ConditionalPairLinear.certificate

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def conditionalQuadratic (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ActualFamily security order :=
  pairQuadraticCertificate security order horder scalar +
    ConditionalPairLinear.certificate security order (by omega) scalar *
      translationCertificate security order (by omega) scalar.val

def conditionalCubic (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ActualFamily security order :=
  pairQuadraticCertificate security order horder scalar * translationCertificate security order (by omega) scalar.val

def legQuadratic (security order : ℕ) (horder : 2 ≤ order) : ActualFamily security order :=
  ∑ scalar, (scalarLaw security).weight scalar • conditionalQuadratic security order horder scalar

def legCubic (security order : ℕ) (horder : 2 ≤ order) : ActualFamily security order :=
  ∑ scalar, (scalarLaw security).weight scalar • conditionalCubic security order horder scalar

def completeLegAtom (security order : ℕ) (horder : 2 ≤ order) : ActualFamily security order :=
  legLinearCertificate security order (by omega) + legQuadratic security order horder + legCubic security order horder

theorem certificateNorm_product (security order : ℕ) (first second : ActualFamily security order) :
    certificateNorm security order (first * second) ≤ certificateNorm security order first * certificateNorm security order second := by
  apply familyNorm_product_le
  · unfold primaryFactor
    positivity
  · unfold bodyFactor radius
    positivity

theorem conditionalQuadratic_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    certificateNorm security order (conditionalQuadratic security order horder scalar) ≤
      2241888 / (Parameters.base security : ℝ) ^ 134 := by
  have hb := FirstResponse.base_pos security
  have hprod := (certificateNorm_product security order
    (ConditionalPairLinear.certificate security order (by omega) scalar)
    (translationCertificate security order (by omega) scalar.val)).trans
      (mul_le_mul (ConditionalPairLinear.certificate_norm security order (by omega) scalar)
        (translationCertificate_norm_decay security order (by omega) scalar.val)
        (certificateNorm_nonneg security order _) (by positivity))
  calc
    _ ≤ certificateNorm security order (pairQuadraticCertificate security order horder scalar) +
        certificateNorm security order (ConditionalPairLinear.certificate security order (by omega) scalar *
          translationCertificate security order (by omega) scalar.val) := certificateNorm_add security order _ _
    _ ≤ 406880 / (Parameters.base security : ℝ) ^ 134 +
        (32768 / (Parameters.base security : ℝ) ^ 55) * (56 / (Parameters.base security : ℝ) ^ 79) :=
      add_le_add (pairQuadraticCertificate_norm security order horder scalar) hprod
    _ = _ := by ring

theorem conditionalCubic_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    certificateNorm security order (conditionalCubic security order horder scalar) ≤
      22785280 / (Parameters.base security : ℝ) ^ 213 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ certificateNorm security order (pairQuadraticCertificate security order horder scalar) *
        certificateNorm security order (translationCertificate security order (by omega) scalar.val) :=
      certificateNorm_product security order _ _
    _ ≤ (406880 / (Parameters.base security : ℝ) ^ 134) * (56 / (Parameters.base security : ℝ) ^ 79) :=
      mul_le_mul (pairQuadraticCertificate_norm security order horder scalar)
        (translationCertificate_norm_decay security order (by omega) scalar.val)
        (certificateNorm_nonneg security order _) (by positivity)
    _ = _ := by ring

theorem legQuadratic_norm (security order : ℕ) (horder : 2 ≤ order) :
    certificateNorm security order (legQuadratic security order horder) ≤
      2241888 / (Parameters.base security : ℝ) ^ 134 :=
  certificateNorm_average_le security order (scalarLaw security) _ _ (conditionalQuadratic_norm security order horder)

theorem legCubic_norm (security order : ℕ) (horder : 2 ≤ order) :
    certificateNorm security order (legCubic security order horder) ≤
      22785280 / (Parameters.base security : ℝ) ^ 213 :=
  certificateNorm_average_le security order (scalarLaw security) _ _ (conditionalCubic_norm security order horder)

theorem legQuadratic_population_bound (security order : ℕ) (horder : 2 ≤ order) :
    (Parameters.legCount security : ℝ) * certificateNorm security order (legQuadratic security order horder) ≤
      2241888 / (Parameters.base security : ℝ) ^ 6 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (2241888 / (Parameters.base security : ℝ) ^ 134) :=
      mul_le_mul_of_nonneg_left (legQuadratic_norm security order horder) (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp

theorem legCubic_population_bound (security order : ℕ) (horder : 2 ≤ order) :
    (Parameters.legCount security : ℝ) * certificateNorm security order (legCubic security order horder) ≤
      22785280 / (Parameters.base security : ℝ) ^ 85 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (22785280 / (Parameters.base security : ℝ) ^ 213) :=
      mul_le_mul_of_nonneg_left (legCubic_norm security order horder) (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp

theorem completeLegAtom_norm (security order : ℕ) (horder : 2 ≤ order) :
    certificateNorm security order (completeLegAtom security order horder) ≤
      43377248 / (Parameters.base security : ℝ) ^ 78 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  calc
    _ ≤ certificateNorm security order (legLinearCertificate security order (by omega) + legQuadratic security order horder) +
        certificateNorm security order (legCubic security order horder) := certificateNorm_add security order _ _
    _ ≤ certificateNorm security order (legLinearCertificate security order (by omega)) +
        certificateNorm security order (legQuadratic security order horder) +
        certificateNorm security order (legCubic security order horder) :=
      add_le_add (certificateNorm_add security order _ _) le_rfl
    _ ≤ 18350080 / (Parameters.base security : ℝ) ^ 78 + 2241888 / (Parameters.base security : ℝ) ^ 134 +
        22785280 / (Parameters.base security : ℝ) ^ 213 :=
      add_le_add (add_le_add (legLinearCertificate_norm_decay security order (by omega)) (legQuadratic_norm security order horder))
        (legCubic_norm security order horder)
    _ ≤ 18350080 / (Parameters.base security : ℝ) ^ 78 + 2241888 / (Parameters.base security : ℝ) ^ 78 +
        22785280 / (Parameters.base security : ℝ) ^ 78 := by
      exact add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega)))) (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega)))
    _ = _ := by ring

theorem completeLegAtom_square_population (security order : ℕ) (horder : 2 ≤ order) :
    (Parameters.legCount security : ℝ) * certificateNorm security order (completeLegAtom security order horder) ^ 2 ≤
      1881585644053504 / (Parameters.base security : ℝ) ^ 28 := by
  have hb := FirstResponse.base_pos security
  have hs := pow_le_pow_left₀ (certificateNorm_nonneg security order _) (completeLegAtom_norm security order horder) 2
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (43377248 / (Parameters.base security : ℝ) ^ 78) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp; ring

end

end CurrentAFT.LegBackgroundFamilies

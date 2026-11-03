import CurrentAFT.GlobalRaising
import CurrentAFT.PrimaryMassFamilies
import CurrentAFT.BackgroundEvaluation
import CurrentAFT.BackgroundFirstEvaluation

/-!
# The actual ordinary group's normalized response

Its signed numerator retains the original safe body slot. The reciprocal
of its positive output polynomial is represented solely by new primary
slots, using the constructed first-primary inverse. Thus reciprocal
corrections do not create body slots.
-/
namespace CurrentAFT.OrdinaryRaising

open AFT DiffuseProfiles ProposalPrimary ActualControls FringeCertificate BackgroundCertificates
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse GradedInverseNorm LocalCoefficientFamily LocalRaisingFirst LocalRaisingBounds
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def deviation (security : ℕ) : Palette security → ℝ :=
  (convolvedCenterLaw security).weight - uniformProfile security

theorem deviation_mass (security : ℕ) : ∑ color, deviation security color = 0 := by
  have hq := (FirstResponse.modulus_pos security).ne'
  simp only [deviation, Pi.sub_apply, uniformProfile, Finset.sum_sub_distrib, FiniteDist.sum_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  norm_num

theorem convolvedCenter_height (security : ℕ) (output : Palette security) :
    (convolvedCenterLaw security).weight output ≤ 4 / (Parameters.modulus security : ℝ) := by
  rw [convolvedCenterLaw_weight]
  unfold rootConvolutionProfile
  calc
    _ ≤ ∑ seed, (actualSeedLaw security).weight seed * (4 / (Parameters.modulus security : ℝ)) := by
      apply Finset.sum_le_sum
      intro seed _
      exact mul_le_mul_of_nonneg_left (centerLaw_height security _) ((actualSeedLaw security).nonneg seed)
    _ = _ := by rw [← Finset.sum_mul, (actualSeedLaw security).sum_one, one_mul]

theorem convolvedCenter_uniform_energy (security : ℕ) :
    profileSquareNorm (uniformReference security).weight (convolvedCenterLaw security).weight ≤ 4 := by
  have h := BlockDensity.profile_energy_le_ratio (uniformReference security).weight
    (convolvedCenterLaw security).weight 4
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (convolvedCenterLaw security).nonneg (fun color => by
      rw [uniformReference_weight]
      exact (convolvedCenter_height security color).trans_eq (by ring))
  simpa only [FiniteDist.sum_one, mul_one] using h

theorem profile_primary_energy_le_uniform (security : ℕ) (profile : Palette security → ℝ) :
    profileSquareNorm (primaryLaw security).weight profile ≤
      2 * profileSquareNorm (uniformReference security).weight profile := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  have hq := FirstResponse.modulus_pos security
  have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight color := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security color
  exact (div_le_div_of_nonneg_left (sq_nonneg (profile color)) (by positivity) hlower).trans_eq (by
    rw [uniformReference_weight]
    ring)

theorem deviation_energy (security : ℕ) : profileSquareNorm (primaryLaw security).weight (deviation security) ≤ 20 := by
  have hself := (profile_primary_energy_le_uniform security (convolvedCenterLaw security).weight).trans
    (mul_le_mul_of_nonneg_left (convolvedCenter_uniform_energy security) (by norm_num : (0 : ℝ) ≤ 2))
  have h := FringeCertificate.profileSquareNorm_sub_le_two security (convolvedCenterLaw security).weight (uniformProfile security)
  exact h.trans (by linarith [uniformProfile_square_le_two security])

def positiveAtom (security order : ℕ) (horder : 1 ≤ order) : Family security order :=
  massCertificateFamily security order 1 horder (oneWordProfile (deviation security))
    (oneWordProfile_centered _ (deviation_mass security)) (oneWordProfile_symmetric _)

theorem positiveAtom_zero (security order : ℕ) (horder : 1 ≤ order) :
    positiveAtom security order horder (zeroArity order) = 0 := by
  unfold positiveAtom massCertificateFamily
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
  change 0 = 1 at h
  omega

theorem positiveAtom_norm (security order : ℕ) (horder : 1 ≤ order) :
    coefficientNorm security order (positiveAtom security order horder) ≤
      40 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> ring
  have henergyEq : massEnergy security 1 (oneWordProfile (deviation security)) =
      profileSquareNorm (primaryLaw security).weight (deviation security) :=
    oneWordProfile_energy (primaryLaw security).weight (deviation security)
  have hsqrt : Real.sqrt (massEnergy security 1 (oneWordProfile (deviation security))) ≤ 5 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, (henergyEq.le.trans (deviation_energy security)).trans (by norm_num)⟩
  have h := massCertificateFamily_norm security order 1 horder
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) hp
    (oneWordProfile (deviation security)) (oneWordProfile_centered _ (deviation_mass security)) (oneWordProfile_symmetric _)
  simp only [pow_one] at h
  calc
    _ ≤ BackgroundRates.primaryFactor security * (2 / activation security) *
        Real.sqrt (massEnergy security 1 (oneWordProfile (deviation security))) := h
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (8 * (Parameters.base security : ℝ)) * 5 :=
      mul_le_mul (mul_le_mul (le_of_eq (BackgroundRates.primaryFactor_eq security)) hinv (by positivity) (by positivity))
        hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp; norm_num

def positiveFamily (security order : ℕ) (horder : 1 ≤ order) : Family security order :=
  1 + positiveAtom security order horder

def positiveInverse (security order : ℕ) (horder : 1 ≤ order) : Family security order :=
  backgroundInverse (primaryLaw security) (bodyReference security) order (positiveFamily security order horder)

theorem positiveFamily_unit_constant (security order : ℕ) (horder : 1 ≤ order) :
    positiveFamily security order horder (zeroArity order) = (1 : Family security order) (zeroArity order) := by
  change (1 : Family security order) (zeroArity order) + positiveAtom security order horder (zeroArity order) = _
  rw [positiveAtom_zero, add_zero]

def normalizedFamily (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) : Family security order :=
  bodyFamily (primaryLaw security) (bodyReference security) order horder score hcentered * positiveInverse security order horder

def raisingFamily (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) : Family security order :=
  bodyFamily (primaryLaw security) (bodyReference security) order horder score hcentered * (positiveInverse security order horder - 1)

theorem normalizedFamily_eq_leading_add (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) :
    normalizedFamily security order horder score hcentered =
      bodyFamily (primaryLaw security) (bodyReference security) order horder score hcentered +
        raisingFamily security order horder score hcentered := by
  unfold normalizedFamily raisingFamily
  rw [mul_sub, mul_one]
  abel

theorem raisingFamily_vanishesBelow (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (raisingFamily security order horder score hcentered) := by
  apply vanishesBelow_mul _ _ order 1 1
  · apply vanishesBelow_one_of_zero
    unfold bodyFamily
    rw [Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun arity : TruncatedArity order => arity.val.2.val) hequal
    change 0 = 1 at h
    omega
  · exact backgroundInverse_sub_one_vanishes _ _ order _ (positiveFamily_unit_constant security order horder)

theorem positiveFamily_image (security order : ℕ) (horder : 1 ≤ order) :
    BackgroundEvaluation.evaluation security order (positiveFamily security order horder) =
      1 + TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm (deviation security)) := by
  unfold positiveFamily positiveAtom
  rw [map_add, map_one, BackgroundEvaluation.massCertificateFamily_image,
    BackgroundFirstEvaluation.massPolynomial_one]

theorem normalizedFamily_mul_positive (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) :
    normalizedFamily security order horder score hcentered * positiveFamily security order horder =
      bodyFamily (primaryLaw security) (bodyReference security) order horder score hcentered := by
  unfold normalizedFamily positiveInverse
  rw [mul_assoc, backgroundInverse_mul _ _ order _ (positiveFamily_unit_constant security order horder), mul_one]

theorem positiveInverse_bounds (security order : ℕ) (horder : 1 ≤ order) :
    coefficientNorm security order (positiveInverse security order horder) ≤ 2 ∧
      coefficientNorm security order (positiveInverse security order horder - 1) ≤
        80 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  have hbody : 0 ≤ BackgroundRates.bodyFactor security := by unfold BackgroundRates.bodyFactor BackgroundRates.radius; positivity
  let theta := 40 / (Parameters.base security : ℝ) ^ 63
  have htheta : 0 ≤ theta := by dsimp only [theta]; positivity
  have htwo : (2 : ℝ) ≤ Parameters.base security := by exact_mod_cast Parameters.base_ge_two security
  have hone : (1 : ℝ) ≤ Parameters.base security := by linarith
  have h7 : (128 : ℝ) ≤ (Parameters.base security : ℝ) ^ 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    norm_num only [show (2 : ℝ) ^ 7 = 128 by norm_num] at h
    exact h
  have hpower : (Parameters.base security : ℝ) ^ 7 ≤ (Parameters.base security : ℝ) ^ 63 :=
    pow_le_pow_right₀ hone (by omega)
  have hhalf : theta ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos hb _)).mpr
    linarith
  have hgap : theta < 1 := by linarith
  have hdefect : coefficientNorm security order (1 - positiveFamily security order horder) ≤ theta := by
    have hequal : (1 - positiveFamily security order horder : Family security order) = -positiveAtom security order horder := by
      unfold positiveFamily
      abel
    rw [hequal]
    unfold LocalRaisingBounds.coefficientNorm
    rw [familyNorm_neg]
    exact positiveAtom_norm security order horder
  constructor
  · apply (backgroundInverse_norm_le _ _ order _ _ hp hbody _ theta hgap hdefect).trans
    apply (div_le_iff₀ (sub_pos.mpr hgap)).mpr
    linarith
  · apply (backgroundInverse_correction_norm_le _ _ order _ _ hp hbody _ theta hgap hdefect).trans
    calc
      _ ≤ theta / (1 / 2) := div_le_div_of_nonneg_left htheta (by norm_num) (by linarith)
      _ = _ := by dsimp only [theta]; ring

theorem raisingFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) :
    coefficientNorm security order (raisingFamily security order horder score hcentered) ≤
      (80 / (Parameters.base security : ℝ) ^ 63) * BackgroundRates.bodyFactor security *
        Real.sqrt ((bodyReference security).l2Sq score) := by
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  have hbody : 0 ≤ BackgroundRates.bodyFactor security := by unfold BackgroundRates.bodyFactor BackgroundRates.radius; positivity
  have hnorm : coefficientNorm security order (bodyFamily (primaryLaw security) (bodyReference security)
      order horder score hcentered) = BackgroundRates.bodyFactor security * Real.sqrt ((bodyReference security).l2Sq score) :=
    bodyFamily_norm _ _ order horder _ _ score hcentered
  unfold LocalRaisingBounds.coefficientNorm at hnorm
  unfold raisingFamily
  apply (familyNorm_product_le _ _ order _ _ hp hbody _ _).trans
  rw [hnorm]
  exact (mul_le_mul_of_nonneg_left (positiveInverse_bounds security order horder).2
    (mul_nonneg hbody (Real.sqrt_nonneg _))).trans_eq (by ring)

def centeredBodyScores (security : ℕ) : Submodule ℝ (SafePalette security → ℝ) where
  carrier := {score | (bodyReference security).expectation score = 0}
  zero_mem' := by simp [FiniteDist.expectation]
  add_mem' {first second} hfirst hsecond := by
    change (bodyReference security).expectation first = 0 at hfirst
    change (bodyReference security).expectation second = 0 at hsecond
    change (bodyReference security).expectation (fun color => first color + second color) = 0
    rw [FiniteDist.expectation_add, hfirst, hsecond, add_zero]
  smul_mem' scalar score hscore := by
    change (bodyReference security).expectation (fun color => scalar * score color) = 0
    rw [FiniteDist.expectation_const_mul, hscore, mul_zero]

def bodyEmbeddingLinear (security order : ℕ) (horder : 1 ≤ order) :
    centeredBodyScores security →ₗ[ℝ] Family security order where
  toFun score := bodyFamily (primaryLaw security) (bodyReference security) order horder score.val score.property
  map_add' first second := by unfold bodyFamily; rw [← Pi.single_add]; rfl
  map_smul' scalar score := by unfold bodyFamily; rw [← Pi.single_smul]; rfl

def raisingLinear (security order : ℕ) (horder : 1 ≤ order) :
    centeredBodyScores security →ₗ[ℝ] Family security order where
  toFun score := raisingFamily security order horder score.val score.property
  map_add' first second := by
    change bodyEmbeddingLinear security order horder (first + second) * _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' scalar score := by
    change bodyEmbeddingLinear security order horder (scalar • score) * _ = _
    rw [map_smul, smul_mul_assoc, RingHom.id_apply]
    rfl

end
end CurrentAFT.OrdinaryRaising


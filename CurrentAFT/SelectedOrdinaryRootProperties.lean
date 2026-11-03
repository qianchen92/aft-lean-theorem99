import CurrentAFT.SelectedOrdinaryRoot
import CurrentAFT.BackgroundFirstEvaluation

/-! # Norm and physical identities of the actual selected ordinary root channel -/
namespace CurrentAFT.SelectedOrdinaryRootProperties

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds PrimaryTensorInverse
  SelectedOrdinaryRoot
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

private theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security := by
  unfold BackgroundRates.primaryFactor
  positivity

private theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security := by
  unfold BackgroundRates.bodyFactor BackgroundRates.radius
  positivity

theorem densityLinear_energy (security : ℕ) (score : Input security → ℝ) :
    (primaryLaw security).l2Sq (densityLinear security score) ≤
      (2 / activation security) ^ 2 * (8 * (inputLaw security).l2Sq score) := by
  rw [densityLinear_apply]
  have hraw : (primaryLaw security).l2Sq
      (fun color => rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color) =
      profileSquareNorm (primaryLaw security).weight (rawMass security (controlCenterLinear security score)) := by
    change densitySquareNorm (primaryLaw security).weight _ = _
    exact densityScore_square _ _
  have h := densityInverse_energy security
    (fun color => rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color)
  rw [hraw] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (rawMass_primary_energy security (controlCenterLinear security score)).trans
    (mul_le_mul_of_nonneg_left (controlCenter_energy_le security score) (by norm_num : (0 : ℝ) ≤ 8))

theorem numerator_norm (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (numeratorLinear security order horder score) ≤
      (24 / (Parameters.base security : ℝ) ^ 63) * Real.sqrt ((inputLaw security).l2Sq score) := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> ring
  have hsqrt := Real.sqrt_le_sqrt (densityLinear_energy security score)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg (by norm_num) ha.le),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)] at hsqrt
  change familyNorm (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (BackgroundFamilies.primaryFamily _ _ order horder (densityLinear security score) (densityLinear_centered security score)) ≤ _
  rw [BackgroundFamilies.primaryFamily_norm]
  calc
    _ ≤ BackgroundRates.primaryFactor security * ((2 / activation security) * Real.sqrt 8 * Real.sqrt ((inputLaw security).l2Sq score)) :=
      by simpa only [FiniteDist.l2Sq, mul_assoc] using mul_le_mul_of_nonneg_left hsqrt (primaryFactor_nonneg security)
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * ((8 * (Parameters.base security : ℝ)) * 3 * Real.sqrt ((inputLaw security).l2Sq score)) := by
      rw [BackgroundRates.primaryFactor_eq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul hinv (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      rw [show (64 : ℕ) = 63 + 1 by omega, pow_add, pow_one]
      field_simp [hb.ne']
      ring

theorem channel_norm (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (channel security order horder score) ≤
      (48 / (Parameters.base security : ℝ) ^ 63) * Real.sqrt ((inputLaw security).l2Sq score) := by
  have hn : 0 ≤ LocalRaisingBounds.coefficientNorm security order (numeratorLinear security order horder score) :=
    familyNorm_nonneg _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _
  change LocalRaisingBounds.coefficientNorm security order
    (numeratorLinear security order horder score * OrdinaryRaising.positiveInverse security order horder) ≤ _
  apply (familyNorm_product_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _).trans
  calc
    _ ≤ LocalRaisingBounds.coefficientNorm security order (numeratorLinear security order horder score) * 2 :=
      mul_le_mul_of_nonneg_left (OrdinaryRaising.positiveInverse_bounds security order horder).1 hn
    _ ≤ ((24 / (Parameters.base security : ℝ) ^ 63) * Real.sqrt ((inputLaw security).l2Sq score)) * 2 :=
      mul_le_mul_of_nonneg_right (numerator_norm security order horder score) (by norm_num)
    _ = _ := by ring

theorem numerator_leading (security : ℕ) (score : Input security → ℝ) :
    activation security • FirstResponse.response security
        (fun color => (primaryLaw security).weight color * densityLinear security score color) =
      rawMass security (controlCenterLinear security score) := by
  have h := densityResponse_inverse security
    (fun color => rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color)
  rw [← densityLinear_apply] at h
  funext color
  have hp := congrFun h color
  rw [densityResponse_apply] at hp
  apply (div_left_inj' (primaryReference_positive security color).ne').mp
  exact hp

theorem numerator_image (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (numeratorLinear security order horder score) =
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.profileForm (rawMass security (controlCenterLinear security score))) := by
  change BackgroundEvaluation.evaluation security order
    (BackgroundFamilies.primaryFamily _ _ order horder (densityLinear security score) (densityLinear_centered security score)) = _
  rw [BackgroundFirstEvaluation.primaryFamily_image, numerator_leading]

theorem channel_physical_identity (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (channel security order horder score) *
      (1 + TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm (OrdinaryRaising.deviation security))) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm
        (rawMass security (controlCenterLinear security score))) := by
  have hmul : channel security order horder score * OrdinaryRaising.positiveFamily security order horder =
      numeratorLinear security order horder score := by
    change (numeratorLinear security order horder score * OrdinaryRaising.positiveInverse security order horder) * _ = _
    unfold OrdinaryRaising.positiveInverse
    rw [mul_assoc, backgroundInverse_mul _ _ order _ (OrdinaryRaising.positiveFamily_unit_constant security order horder), mul_one]
  have h := congrArg (BackgroundEvaluation.evaluation security order) hmul
  rwa [map_mul, OrdinaryRaising.positiveFamily_image, numerator_image] at h

theorem channel_vanishesBelow_one (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (channel security order horder score) := by
  apply vanishesBelow_mul _ _ order 1 0
  · apply vanishesBelow_one_of_zero
    change BackgroundFamilies.primaryFamily _ _ order horder (densityLinear security score) (densityLinear_centered security score)
      (zeroArity order) = 0
    unfold BackgroundFamilies.primaryFamily
    rw [Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
    change 0 = 1 at h
    omega
  · exact vanishesBelow_zero _ _ order _

theorem channel_no_body (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 0 (channel security order horder score) := by
  have hnum := RaisingBodySlots.primaryFamily_atMost security order horder (densityLinear security score) (densityLinear_centered security score)
  have hatom : RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 0
      (OrdinaryRaising.positiveAtom security order horder) :=
    RaisingBodySlots.atMost_single _ _ order (PrimaryMassFamilies.primaryArity order 1 horder) _
  have hpositive := RaisingBodySlots.atMost_add _ _ order 0 _ _ (RaisingBodySlots.atMost_one _ _ order) hatom
  exact RaisingBodySlots.atMost_mul _ _ order 0 0 _ _ hnum
    (RaisingBodySlots.atMost_inverse _ _ order (OrdinaryRaising.positiveFamily security order horder) hpositive)

end
end CurrentAFT.SelectedOrdinaryRootProperties

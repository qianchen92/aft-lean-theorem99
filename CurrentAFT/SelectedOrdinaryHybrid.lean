import CurrentAFT.SelectedOrdinaryMean

/-! # The selected ordinary group with a retained leading body slot

Root averaging retains the original body coefficient. Root-centered
responses use the actual pure-primary inverse. Their sum is a genuine
linear lift of the same physical root/control experiment.
-/
namespace CurrentAFT.SelectedOrdinaryHybrid
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingFirst LocalRaisingBounds CoefficientHilbert
  SelectedOrdinaryRoot SelectedOrdinaryMean
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference

private theorem hp (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security :=
  (RaisingPatternBudget.primaryFactor_pos security).le
private theorem hb (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security :=
  (RaisingPatternBudget.bodyFactor_pos security).le

def independentChannel (security order : ℕ) (horder : 1 ≤ order) :
    (SafePalette security → ℝ) →ₗ[ℝ] Family security order where
  toFun score := RaisingChannels.bodyLeading security order horder score * OrdinaryRaising.positiveInverse security order horder
  map_add' first second := by rw [map_add, add_mul]
  map_smul' scalar score := by rw [map_smul, smul_mul_assoc, RingHom.id_apply]

theorem independentChannel_eq (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    independentChannel security order horder score = OrdinaryRaising.normalizedFamily security order horder
      (centerLinear (bodyReference security) score) (center_mean _ score) := rfl

theorem independentChannel_eq_leading_add_raised (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    independentChannel security order horder score = RaisingChannels.bodyLeading security order horder score +
      RaisingChannels.bodyRaised security order horder score := by
  exact OrdinaryRaising.normalizedFamily_eq_leading_add security order horder _ _

theorem independentChannel_norm (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    coefficientNorm security order (independentChannel security order horder score) ≤
      (2 * BackgroundRates.bodyFactor security) * Real.sqrt ((bodyReference security).l2Sq score) := by
  have hn := familyNorm_nonneg (primaryLaw security) (bodyReference security) order _ _ (hp security) (hb security)
    (RaisingChannels.bodyLeading security order horder score)
  apply (familyNorm_product_le _ _ order _ _ (hp security) (hb security) _ _).trans
  calc
    _ ≤ coefficientNorm security order (RaisingChannels.bodyLeading security order horder score) * 2 :=
      mul_le_mul_of_nonneg_left (OrdinaryRaising.positiveInverse_bounds security order horder).1 hn
    _ ≤ (BackgroundRates.bodyFactor security * Real.sqrt ((bodyReference security).l2Sq score)) * 2 :=
      mul_le_mul_of_nonneg_right (RaisingChannels.bodyLeading_norm security order horder score) (by norm_num)
    _ = _ := by ring

def channel (security order : ℕ) (horder : 1 ≤ order) : (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (independentChannel security order horder).comp (rootMean security) +
    (SelectedOrdinaryRoot.channel security order horder).comp (rootCenter security)

theorem channel_apply (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    channel security order horder score = independentChannel security order horder (rootMean security score) +
      SelectedOrdinaryRoot.channel security order horder (rootCenter security score) := rfl

theorem channel_constant (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    channel security order horder (constantRoot security score) = independentChannel security order horder score := by
  rw [channel_apply, rootMean_constant, rootCenter_constant, map_zero, add_zero]

theorem channel_on_centered (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ)
    (hcentered : ∀ center, (rootReference security).expectation (fun root => score (root, center)) = 0) :
    channel security order horder score = SelectedOrdinaryRoot.channel security order horder score := by
  rw [channel_apply, rootMean_zero_of_centered security score hcentered,
    rootCenter_eq_of_centered security score hcentered, map_zero, zero_add]

theorem channel_norm (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    coefficientNorm security order (channel security order horder score) ≤
      (2 * BackgroundRates.bodyFactor security + 48 / (Parameters.base security : ℝ)^63) *
        Real.sqrt ((inputLaw security).l2Sq score) := by
  rw [channel_apply]
  apply (familyNorm_add_le _ _ order _ _ (hp security) (hb security) _ _).trans
  apply (add_le_add (independentChannel_norm security order horder _) (SelectedOrdinaryRootProperties.channel_norm security order horder _)).trans
  calc
    _ ≤ (2 * BackgroundRates.bodyFactor security) * Real.sqrt ((inputLaw security).l2Sq score) +
        (48 / (Parameters.base security : ℝ)^63) * Real.sqrt ((inputLaw security).l2Sq score) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (rootMean_energy_le security score)) (mul_nonneg (by norm_num) (hb security)))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (rootCenter_energy_le security score)) (by positivity))
    _ = _ := by ring

theorem channel_norm_coarse (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    coefficientNorm security order (channel security order horder score) ≤
      (50 / (Parameters.base security : ℝ)^63) * Real.sqrt ((inputLaw security).l2Sq score) := by
  have hone : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hfactor : BackgroundRates.bodyFactor security ≤ 1 / (Parameters.base security : ℝ)^63 :=
    (BackgroundRates.bodyFactor_le security).trans (one_div_le_one_div_of_le
      (pow_pos (FirstResponse.base_pos security) _) (pow_le_pow_right₀ hone (by omega)))
  apply (channel_norm security order horder score).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc
    _ ≤ 2 * (1 / (Parameters.base security : ℝ)^63) + 48 / (Parameters.base security : ℝ)^63 := by linarith
    _ = _ := by ring

theorem independentChannel_physical (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    BackgroundEvaluation.evaluation security order (independentChannel security order horder score) *
      (1 + TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm (OrdinaryRaising.deviation security))) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm
        (MarkedPairLeading.bodyConvolution security (BodyChannelEvaluation.safeMass security (centerLinear (bodyReference security) score)))) := by
  have h := congrArg (BackgroundEvaluation.evaluation security order)
    (OrdinaryRaising.normalizedFamily_mul_positive security order horder (centerLinear (bodyReference security) score) (center_mean _ score))
  rw [map_mul, OrdinaryRaising.positiveFamily_image, BodyChannelEvaluation.bodyFamily_image] at h
  exact h

theorem channel_physical_identity (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (channel security order horder score) *
      (1 + TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm (OrdinaryRaising.deviation security))) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm
        (rawMass security (controlCenterLinear security score))) := by
  rw [channel_apply, map_add, add_mul, independentChannel_physical,
    SelectedOrdinaryRootProperties.channel_physical_identity]
  rw [← rawMass_constant, ← controlCenter_constant]
  rw [← map_add, ← map_add]
  change TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm
    (rawMassLinear security (controlCenterLinear security (constantRoot security (rootMean security score))) +
      rawMassLinear security (controlCenterLinear security (rootCenter security score)))) = _
  rw [← map_add, ← map_add]
  have hsplit : constantRoot security (rootMean security score) + rootCenter security score = score := by
    change constantRoot security (rootMean security score) + (score - constantRoot security (rootMean security score)) = score
    abel
  rw [hsplit]
  rfl

theorem independentChannel_vanishesBelow_one (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (independentChannel security order horder score) := by
  apply vanishesBelow_mul _ _ order 1 0
  · apply vanishesBelow_one_of_zero
    change BackgroundFamilies.bodyFamily _ _ order horder _ _ (zeroArity order) = 0
    unfold BackgroundFamilies.bodyFamily
    rw [Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun arity : TruncatedArity order => arity.val.2.val) hequal
    change 0 = 1 at h
    omega
  · exact vanishesBelow_zero _ _ order _

theorem channel_vanishesBelow_one (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (channel security order horder score) := by
  rw [channel_apply]
  exact vanishesBelow_add _ _ order 1 _ _ (independentChannel_vanishesBelow_one security order horder _)
    (SelectedOrdinaryRootProperties.channel_vanishesBelow_one security order horder _)

theorem channel_no_new_body (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 1 (channel security order horder score) := by
  rw [channel_apply]
  apply RaisingBodySlots.atMost_add
  · have hatom : RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 0
        (OrdinaryRaising.positiveAtom security order horder) :=
      RaisingBodySlots.atMost_single _ _ order (PrimaryMassFamilies.primaryArity order 1 horder) _
    have hpositive := RaisingBodySlots.atMost_add _ _ order 0 _ _ (RaisingBodySlots.atMost_one _ _ order) hatom
    exact RaisingBodySlots.atMost_mul _ _ order 1 0 _ _
      (RaisingBodySlots.bodyFamily_atMost security order horder _ _)
      (RaisingBodySlots.atMost_inverse _ _ order _ hpositive)
  · intro arity hbody
    exact SelectedOrdinaryRootProperties.channel_no_body security order horder _ arity (by omega)

theorem channel_centered_no_body (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ)
    (hcentered : ∀ center, (rootReference security).expectation (fun root => score (root, center)) = 0) :
    RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 0 (channel security order horder score) := by
  rw [channel_on_centered security order horder score hcentered]
  exact SelectedOrdinaryRootProperties.channel_no_body security order horder _

end
end CurrentAFT.SelectedOrdinaryHybrid

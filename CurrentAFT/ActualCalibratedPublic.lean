import CurrentAFT.ActualPublicExperiment
import CurrentAFT.ActualCalibrationRates
import CurrentAFT.FiniteZeroSum

/-! # Positive publicly charged sampling with the actual calibrated weight -/
namespace CurrentAFT.ActualCalibratedPublic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge ActualPublicExperiment
  ActualCalibrationFourier ActualCalibrationRates ActualCalibrationClipping ActualCompleteStability
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance endpointNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by exact_mod_cast PhysicalFockRates.dimension_pos security⟩⟩

def weight (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) : Core security → ℝ :=
  pulledWeight security order (calibratedCoefficients security order horder hsecurity layout)

def mass (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) :
    (Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)) → ℝ :=
  endpointMass (proposal security) (weight security order horder hsecurity layout) (channel security layout)

/-- The sole algebraic premise left to the complete physical PGF identity. -/
def Calibrated (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) : Prop :=
  TruncatedOutput.quotientMap order
    (RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight
      (ActualWeightedFourier.mixedMass security order (room security order horder hsecurity) layout
        (calibratedCoefficients security order horder hsecurity layout))) = 1

theorem mass_one (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) :
    (∑ word, mass security order horder hsecurity layout word) = 1 := by
  unfold mass
  rw [endpointMass_sum]
  exact (pulledWeight_mean security order _).trans
    (coefficients_scalar security order horder hsecurity (ActualLayouts.blockLayout layout))

theorem clipping_loss (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) :
    clippingLoss (proposal security) (weight security order horder hsecurity layout) =
      loss security order horder hsecurity (ActualLayouts.blockLayout layout) := by
  unfold weight
  rw [pulledWeight_clippingLoss]
  rfl

theorem ambient_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff, ∀ hsecurity : threshold order horder ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      Calibrated security order horder hsecurity layout →
      (∑ word, |mass security order horder hsecurity layout word -
        (FiniteDist.uniform (Fin (Parameters.dimension security) → ZMod (Parameters.modulus security))).weight word|) ≤
          fourierError security order := by
  obtain ⟨cutoff, hcutoff⟩ := tail_of_physical_calibration_eventually order horder
  refine ⟨cutoff, ?_⟩
  intro security hlarge hsecurity layout hcalibrated
  have htail := hcutoff security hlarge hsecurity layout hcalibrated
  have htail' : (∑ frequency ∈ Finset.univ.erase
      (0 : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)),
      ‖signedFourier (mass security order horder hsecurity layout) (coordinateCharacter frequency)‖ ^ 2) ≤
        energyBudget order / ActualPhysicalTail.analysisRadius security ^ (2 * (order + 1)) := by
    simp only [mass, weight, ActualPublicExperiment.signed_fourier]
    exact PublicAuxiliaryFubini.sum_erase_le_enumeration _ _ _ htail
  have hhalf := coordinate_ambient_signed_half_l1 (mass security order horder hsecurity layout)
    (mass_one security order horder hsecurity layout)
  have hroot := Real.sqrt_le_sqrt htail'
  change _ ≤ Real.sqrt _
  simp only [uniformDeviation, FiniteDist.uniform_weight] at hhalf ⊢
  nlinarith only [hhalf, hroot]

theorem positive_eventually (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      Calibrated security (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) hsecurity layout →
      ∃ hpositive : 0 < publicCoreMass (proposal security)
          (weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security),
        1 / (2 * (Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security)
          (weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security) ∧
        ((positivePublicCoreLaw (proposal security)
            (weight security (Parameters.calibrationOrder accuracyOrder)
              (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security) hpositive).mix
          (channel security layout)).totalVariation
            (FiniteZeroSum.uniformLaw (Index := Fin (Parameters.dimension security)) (Parameters.modulus security)) ≤
              2 * (Parameters.modulus security : ℝ) *
                (fourierError security (Parameters.calibrationOrder accuracyOrder) +
                  loss security (Parameters.calibrationOrder accuracyOrder)
                    (calibrationOrder_at_least_two accuracyOrder) hsecurity (ActualLayouts.blockLayout layout)) := by
  obtain ⟨ambientCutoff, hambient⟩ := ambient_eventually (Parameters.calibrationOrder accuracyOrder)
    (calibrationOrder_at_least_two accuracyOrder)
  obtain ⟨smallCutoff, hsmall⟩ := conditioning_small_eventually accuracyOrder
  refine ⟨max ambientCutoff smallCutoff, ?_⟩
  intro security hlarge hsecurity layout hcalibrated
  have ha := hambient security ((le_max_left _ _).trans hlarge) hsecurity layout hcalibrated
  have hs := hsmall security ((le_max_right _ _).trans hlarge) hsecurity (ActualLayouts.blockLayout layout)
  obtain ⟨hpositive, hlower, herror⟩ := FiniteZeroSum.bounded_public_conditioning (Parameters.modulus security)
    (proposal security) (weight security (Parameters.calibrationOrder accuracyOrder)
      (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (channel security layout) (publicCharge security)
    (channel_charge security layout) (fourierError security (Parameters.calibrationOrder accuracyOrder) / 2)
    (loss security (Parameters.calibrationOrder accuracyOrder) (calibrationOrder_at_least_two accuracyOrder)
      hsecurity (ActualLayouts.blockLayout layout)) (ha.trans_eq (by ring))
    (clipping_loss security _ _ hsecurity layout).le (by linarith only [hs])
  refine ⟨hpositive, hlower, herror.trans_eq ?_⟩
  ring

def PositiveConclusion (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security) (layout : RoleIndex security ≃ BodyIndex security)
    (error : ℝ) : Prop :=
  ∃ hpositive : 0 < publicCoreMass (proposal security) (weight security order horder hsecurity layout) (publicCharge security),
    1 / (2 * (Parameters.modulus security : ℝ)) ≤
        publicCoreMass (proposal security) (weight security order horder hsecurity layout) (publicCharge security) ∧
      ((positivePublicCoreLaw (proposal security) (weight security order horder hsecurity layout)
          (publicCharge security) hpositive).mix (channel security layout)).totalVariation
        (FiniteZeroSum.uniformLaw (Index := Fin (Parameters.dimension security)) (Parameters.modulus security)) ≤ error

theorem inversePower_two_steps (security exponent : ℕ) :
    4 * inversePower security (exponent + 2) ≤ inversePower security exponent := by
  have hb := FirstResponse.base_pos security
  have hb2 : (2 : ℝ) ≤ Parameters.base security := by exact_mod_cast Parameters.base_ge_two security
  unfold inversePower
  rw [← mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ (pow_pos hb _) (pow_pos hb _)).mpr
  rw [pow_add]
  have hsquare : (4 : ℝ) ≤ (Parameters.base security : ℝ)^2 := by
    nlinarith [sq_nonneg ((Parameters.base security : ℝ) - 2)]
  have hpower := mul_le_mul_of_nonneg_left hsquare (pow_nonneg hb.le exponent)
  nlinarith only [hpower]

/-- For each fixed requested accuracy, the actual positive public core
achieves that inverse-power total-variation error at every fixed layout. -/
theorem negligible_eventually (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      Calibrated security (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) hsecurity layout →
      PositiveConclusion security (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) hsecurity layout (inversePower security accuracyOrder) := by
  obtain ⟨positiveCutoff, hpositive⟩ := positive_eventually accuracyOrder
  obtain ⟨fourierCutoff, hfourier⟩ := Filter.eventually_atTop.mp (charged_fourier_eventually accuracyOrder)
  obtain ⟨clipCutoff, hclip⟩ := charged_loss_negligible (Parameters.calibrationOrder accuracyOrder)
    (calibrationOrder_at_least_two accuracyOrder) (accuracyOrder + 2)
  refine ⟨max positiveCutoff (max fourierCutoff clipCutoff), ?_⟩
  intro security hlarge hsecurity layout hcalibrated
  obtain ⟨hcore, hlower, herror⟩ := hpositive security ((le_max_left _ _).trans hlarge)
    hsecurity layout hcalibrated
  have hf := hfourier security ((le_max_left _ _).trans ((le_max_right _ _).trans hlarge))
  have hc := hclip security ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
    hsecurity (ActualLayouts.blockLayout layout)
  refine ⟨hcore, hlower, herror.trans ?_⟩
  apply (show 2 * (Parameters.modulus security : ℝ) *
      (fourierError security (Parameters.calibrationOrder accuracyOrder) +
        loss security (Parameters.calibrationOrder accuracyOrder) (calibrationOrder_at_least_two accuracyOrder)
          hsecurity (ActualLayouts.blockLayout layout)) ≤ 4 * inversePower security (accuracyOrder + 2) by
    nlinarith only [hf, hc]).trans
  exact inversePower_two_steps security accuracyOrder

end
end CurrentAFT.ActualCalibratedPublic

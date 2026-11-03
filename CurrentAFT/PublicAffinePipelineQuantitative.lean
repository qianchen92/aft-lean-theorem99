import CurrentAFT.PublicAffinePipelineAccuracy
import CurrentAFT.ActualGaussianRemainder

/-! Quantitative form of the full emitted Gaussian law, with separate fixed-order
Fourier, uniform analytical remainder, and numerical implementation budgets. -/
namespace CurrentAFT.PublicAffinePipeline
open AFT ActualPublicCharge ActualCompleteStability ActualGaussianAccuracy ActualCalibrationRates
open Filter
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current

theorem quantitative_eventually (accuracyOrder : ℕ)
    (producer : ∀ security, Producer security (Parameters.calibrationOrder accuracyOrder))
    (weightError : ℕ → ℝ) (hnonneg : ∀ security, 0≤weightError security)
    (hweight : ∀ᶠ security : ℕ in atTop,
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder)≤security,
      ∀ (layout : CurrentLayoutDraw.Cache security) (core : Core security),
        |(BinaryPublicRejection.coreWeight security security (Parameters.calibrationOrder accuracyOrder)
          (producer security layout).value core:ℝ)-
          ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout.layout core|≤weightError security) :
    ∀ᶠ security : ℕ in atTop,
      (fairGaussian security (Parameters.calibrationOrder accuracyOrder) (producer security)).totalVariation
        (CurrentZeroFiber.uniformFiber security) ≤
      (2*fourierConstant (Parameters.calibrationOrder accuracyOrder))*(Parameters.modulus security:ℝ)*
        (Parameters.base security:ℝ)^(-((Parameters.calibrationOrder accuracyOrder+1:ℕ):ℝ)/4)+
      ActualGaussianRemainder.remainder security (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder)+CurrentMaterializedCompletion.totalError security (weightError security) := by
  obtain ⟨cutoff,hcutoff⟩ := gaussian_bound_eventually accuracyOrder
  filter_upwards [eventually_ge_atTop cutoff,eventually_ge_atTop 1,
    eventually_ge_atTop (threshold (Parameters.calibrationOrder accuracyOrder) (calibrationOrder_at_least_two accuracyOrder)),hweight]
    with security hlarge hs ht hw
  apply gaussian_accuracy
  intro layout
  obtain ⟨hpositive,hmass,hbound⟩ := hcutoff security hlarge ht layout.layout
  rw [fixedGaussian_eq]
  have hlower : 1/(4*(Parameters.modulus security:ℝ)) ≤ 1/(2*(Parameters.modulus security:ℝ)) := by
    have hq : (0:ℝ)<Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.pos
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  apply (CurrentMaterializedCompletion.gaussian_error security (Parameters.calibrationOrder accuracyOrder) hs layout.layout
    (producer security layout).value _ (weightError security) _ (hnonneg security) (hw ht layout) hpositive
    (hlower.trans hmass) hbound).trans
  exact add_le_add (ActualGaussianRemainder.analytic_le security (Parameters.calibrationOrder accuracyOrder)
    (calibrationOrder_at_least_two accuracyOrder) ht (ActualLayouts.blockLayout layout.layout)) le_rfl

/-- A negligible implementation error meets the manuscript's numerical budget
for each fixed requested precision, without changing the calibration order. -/
theorem negligible_quarter_base {error : ℕ → ℝ} (hnegligible : Negligible error) (order : ℕ) :
    ∀ᶠ security : ℕ in atTop, |error security|≤(1/4:ℝ)/(Parameters.base security:ℝ)^order := by
  filter_upwards [hnegligible (order+1),eventually_ge_atTop (max 2 (4*2^order))] with security he hs
  have hs2 : 2≤security := (le_max_left _ _).trans hs
  have hsn : 4*2^order≤security := (le_max_right _ _).trans hs
  have hp : (0:ℝ)<security := by exact_mod_cast (show 0<security by omega)
  have hb : (Parameters.base security:ℝ)≤2*security := by
    exact_mod_cast (show Parameters.base security≤2*security by unfold Parameters.base; omega)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (Parameters.base security)) hb order
  have hfour : (4:ℝ)*2^order≤security := by exact_mod_cast hsn
  apply he.trans
  rw [pow_succ]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hp _) hp) (pow_pos (FirstResponse.base_pos security) _)).mpr
  rw [mul_pow] at hpow
  nlinarith [mul_le_mul_of_nonneg_right hfour (pow_nonneg hp.le order)]

end
end CurrentAFT.PublicAffinePipeline

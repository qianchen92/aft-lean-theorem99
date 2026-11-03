import CurrentAFT.CurrentProtectedSampleFubini
import CurrentAFT.AffineActivationFubini
import CurrentAFT.ActualCalibrationExact
import CurrentAFT.FiniteEnumeration
import CurrentAFT.CurrentSourceTail

/-! # Actual Gaussian affine transport under the complete positive public law

All physical, calibration, source-protection, carry and zero-fiber premises
are discharged here. This analytic finite public law is not yet the full
finite-bit polynomial-time sampler required by the constructive theorem.
-/
namespace CurrentAFT.ActualGaussianAffine
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineTransport CurrentPublicAffineSample CurrentZeroFiber CurrentProtectedSampleFubini
  ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩
local instance dimensionNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by rw [← LobsterCoordinates.current_vertex_count security]; omega⟩⟩

theorem refined_channel_weight (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (word : Word security) :
    (FiniteDist.retype (RefinedPublicOutput.mappedChannel security layout core) :
      FiniteDist (Word security)).weight word =
      (ActualPublicExperiment.channel security layout core).weight word := by
  unfold RefinedPublicOutput.mappedChannel ActualPublicExperiment.channel ActualPublicExperiment.paletteChannel
  simp only [FiniteDist.map_weight, FiniteDist.retype_weight]
  apply Finset.sum_congr (by ext source; simp)
  intro source _
  have he : PublicEndpointFourier.wordEquiv (ZMod.finEquiv (Parameters.modulus security)).toEquiv source =
      (fun index => RefinedPublicOutput.embed security (source index)) := by
    funext index
    rfl
  rw [he]
  split_ifs <;> rfl

/-- The actual protected affine endpoints have exactly the positive
calibrated endpoint law used in the Fourier and clipping proof. -/
theorem protectedEndpoint_eq_calibrated (security order : ℕ)
    (coefficient : ActualControls.Coefficients security order)
    (layout : RoleIndex security ≃ BodyIndex security)
    (hpositive : 0 < publicCoreMass (proposal security) (pulledWeight security order coefficient) (publicCharge security)) :
    protectedEndpointLaw security layout (pulledWeight security order coefficient) hpositive =
      (positivePublicCoreLaw (proposal security) (pulledWeight security order coefficient)
        (publicCharge security) hpositive).mix (ActualPublicExperiment.channel security layout) := by
  rw [protectedEndpoint_eq_completed]
  ext word
  have h := congrArg (fun distribution =>
      (FiniteDist.retype distribution : FiniteDist (Word security)).weight word)
    (AffineActivationFubini.positive_core_completed_output security order coefficient layout hpositive)
  simp only [FiniteDist.retype_weight, FiniteDist.mix_weight] at h
  simp only [FiniteDist.mix_weight, FiniteDist.retype_weight]
  calc
    _ = ∑ core, (positivePublicCoreLaw (proposal security) (pulledWeight security order coefficient)
          (publicCharge security) hpositive).weight core *
        (FiniteDist.retype (RefinedPublicOutput.mappedChannel security layout core) :
          FiniteDist (Word security)).weight word := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro core _
      rw [refined_channel_weight]

/-- The complete current response, its unique calibrated weight, the actual
public graph completion, and the original hidden Gaussian source. -/
theorem gaussian_transport_exists (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∃ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
          (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∃ hpositive : 0 < publicCoreMass (proposal security)
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security),
        1 / (2 * (Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security)
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) (publicCharge security) ∧
        (gaussianLaw security layout
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) hpositive).totalVariation
          (uniformFiber security) ≤ inversePower security accuracyOrder + CurrentSourceProtection.budget security := by
  obtain ⟨cutoff, hcutoff⟩ := ActualCalibrationExact.positive_protected_eventually accuracyOrder
  refine ⟨max cutoff (threshold _ (calibrationOrder_at_least_two accuracyOrder)), ?_⟩
  intro security hlarge
  have hsecurity := (le_max_right _ _).trans hlarge
  refine ⟨hsecurity, ?_⟩
  intro layout
  obtain ⟨hcore, hlower, herror⟩ := hcutoff security ((le_max_left _ _).trans hlarge) hsecurity layout
  refine ⟨hcore, hlower, ?_⟩
  apply gaussian_fiber_bound
  unfold ActualCalibratedPublic.weight
  rw [protectedEndpoint_eq_calibrated]
  exact herror

end
end CurrentAFT.ActualGaussianAffine

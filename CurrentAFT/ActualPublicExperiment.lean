import CurrentAFT.RefinedPublicDisintegration
import CurrentAFT.PublicEndpointFourier

/-! # One source-independent public proposal for charge and Fourier calibration -/
namespace CurrentAFT.ActualPublicExperiment
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  PublicOutputExperiment PublicEndpointFourier RefinedPublicDisintegration FourierCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Residue (security : ℕ) := ZMod (Parameters.modulus security)

private theorem fourier_decision {Color Index : Type*} [Fintype Color] [Fintype Index]
    {modulus : ℕ} [NeZero modulus] (first second : DecidableEq Index)
    (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℂ) (frequency : Index → ZMod modulus) :
    @FourierCoordinates.fourier Color Index _ _ first modulus _ palette mass frequency =
      @FourierCoordinates.fourier Color Index _ _ second modulus _ palette mass frequency := by
  cases Subsingleton.elim first second
  rfl

def paletteChannel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) : FiniteDist (Fin (Parameters.dimension security) → Palette security) :=
  FiniteDist.retype (RefinedPublicOutput.lawGiven security layout core)

def channel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) : FiniteDist (Fin (Parameters.dimension security) → Residue security) :=
  (paletteChannel security layout core).map
    (wordEquiv (ZMod.finEquiv (Parameters.modulus security)).toEquiv)

theorem channel_charge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    (channel security layout core).eventMass (fun word => ∑ index, word index = 0) =
      if publicCharge security core then 1 else 0 := by
  have hpalette : FiniteDist.HasValue (paletteChannel security layout core)
      (fun word => ∑ index, RefinedPublicOutput.embed security (word index)) (chargeValue security core) := by
    intro word hweight
    exact RefinedPublicOutput.lawGiven_charge security layout core word hweight
  have hmapped : FiniteDist.HasValue (channel security layout core) (fun word => ∑ index, word index)
      (chargeValue security core) := by
    apply FiniteDist.HasValue.map
    exact hpalette
  exact FiniteDist.HasValue.eventMass_eq _ _ _ hmapped (fun value => value = 0)

/-- This identity holds for every weight on the old public controls,
including the same signed correction, its clipping, and moment tests. -/
theorem palette_mass (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : PublicWord security → ℝ) (word : Fin (Parameters.dimension security) → Palette security) :
    endpointMass (proposal security) (fun core => weight core.controls) (paletteChannel security layout) word =
      endpointMass (PublicOutputExperiment.reference security) weight
        (PublicSignedOutput.lawGiven security layout) word := by
  unfold endpointMass
  simp_rw [mul_assoc]
  change (proposal security).expectation (fun core => weight core.controls *
    (paletteChannel security layout core).weight word) =
      (PublicOutputExperiment.reference security).expectation (fun controls => weight controls *
        (PublicSignedOutput.lawGiven security layout controls).weight word)
  rw [proposal_weighted_channel]
  apply congrArg (FiniteDist.expectation _)
  funext controls
  apply congrArg (fun value : ℝ => weight controls * value)
  exact refined_average security layout controls word

theorem signed_palette_mass (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order) (word : Fin (Parameters.dimension security) → Palette security) :
    endpointMass (proposal security) (pulledWeight security order coefficient) (paletteChannel security layout) word =
      PublicSignedOutput.signedMass security order layout coefficient word := by
  exact (palette_mass security layout (actualWeight security order coefficient) word).trans (by
    unfold endpointMass PublicSignedOutput.signedMass FiniteDist.expectation
    simp only [mul_assoc])

theorem signed_mass (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order) (word : Fin (Parameters.dimension security) → Residue security) :
    endpointMass (proposal security) (pulledWeight security order coefficient) (channel security layout) word =
      PublicSignedOutput.signedMass security order layout coefficient
        ((wordEquiv (ZMod.finEquiv (Parameters.modulus security)).toEquiv).symm word) := by
  unfold channel
  rw [PublicEndpointFourier.mapped_mass]
  exact signed_palette_mass security order layout coefficient _

theorem signed_fourier (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order) (frequency : Fin (Parameters.dimension security) → Residue security) :
    signedFourier (endpointMass (proposal security) (pulledWeight security order coefficient) (channel security layout))
      (coordinateCharacter frequency) = PublicSignedOutput.coefficient security order layout coefficient frequency := by
  have hmass := funext (signed_mass security order layout coefficient)
  rw [hmass]
  apply Eq.trans (PublicEndpointFourier.fourier_relabel (ZMod.finEquiv (Parameters.modulus security)).toEquiv _ frequency)
  unfold PublicSignedOutput.coefficient
  exact fourier_decision _ _ _ _ _

/-- The public core is accepted and normalized before the protected
channel is applied. Charge consistency is proved for the real channel. -/
theorem positive_core_mix (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order)
    (hpositive : 0 < publicCoreMass (proposal security) (pulledWeight security order coefficient) (publicCharge security)) :
    (positivePublicCoreLaw (proposal security) (pulledWeight security order coefficient) (publicCharge security) hpositive).mix
      (channel security layout) =
      positiveEndpointLaw (proposal security) (pulledWeight security order coefficient) (channel security layout)
        (fun word => ∑ index, word index = 0)
        (by rw [chargedMass_eq_publicCoreMass _ _ _ _ _ (channel_charge security layout)]; exact hpositive) :=
  positivePublicCoreLaw_mix _ _ _ _ _ (channel_charge security layout) hpositive

end
end CurrentAFT.ActualPublicExperiment

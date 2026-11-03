import CurrentAFT.CoefficientOutputFock
import CurrentAFT.FourierSupportIsometry

/-!
# Complete weighted Fourier bound of the actual finite physical coefficient family

The common protected queue scalar and the independent whole-body permutation
are averaged after the complete physical response. The final independent
uniform endpoint permutation is literal finite symmetrization. Every
frequency, including zero and full support, occurs in the resulting bound.
-/

namespace CurrentAFT.ActualWeightedFourier

open AFT DiffuseProfiles ProposalPrimary ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean PhysicalFockRates ActualFockBound ControlCoordinates ControlNorm
  CoefficientOutputFock
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

def randomizationLaw (security : ℕ) :
    FiniteDist (FirstHistogram.Scalar security × Equiv.Perm (BodyIndex security)) :=
  (scalarLaw security).prod (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))

def mixedMass (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order)
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) : ℝ :=
  (randomizationLaw security).expectation (fun sample =>
    familyMass security order hroom layout sample.1.val sample.2 coefficient word)

/-- The full signed endpoint law after the independent final permutation. -/
def signedOutputMass (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order) :
    (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) → ℝ :=
  HistogramNormalization.symmetrizedMass (mixedMass security order hroom layout coefficient)

theorem current_signed_fock_eventually (order : ℕ) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ hroom : 2 * order ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∀ coefficient : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order,
      energy (LocalReferenceEnergy.uniformReference security) (signedOutputMass security order hroom layout coefficient)
        (BackgroundRates.radius security) ≤
        (normConstant order 1 * coefficientNorm (primaryLaw security) (ActualControls.bodyReference security)
          order (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) coefficient) ^ 2 := by
  obtain ⟨threshold, hthreshold⟩ := current_coefficient_fock_eventually order 1 (by norm_num)
  refine ⟨threshold, ?_⟩
  intro security hsecurity hroom layout coefficient
  rw [signedOutputMass, energy_symmetrized]
  apply (energy_average_le (randomizationLaw security) (LocalReferenceEnergy.uniformReference security)
    (fun sample => familyMass security order hroom layout sample.1.val sample.2 coefficient)
    (BackgroundRates.radius security) (radius_nonneg security)).trans
  calc
    _ ≤ (randomizationLaw security).expectation (fun _ =>
        (normConstant order 1 * coefficientNorm (primaryLaw security) (ActualControls.bodyReference security)
          order (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) coefficient) ^ 2) := by
      apply Finset.sum_le_sum
      intro sample _
      apply mul_le_mul_of_nonneg_left _ ((randomizationLaw security).nonneg sample)
      simpa only [one_mul] using hthreshold security hsecurity hroom layout sample.1.val sample.2 coefficient
    _ = _ := FiniteDist.expectation_const _ _

/-- The full weighted Fourier norm is proved from the actual physical
coefficient bounds. It is not supplied as a premise, and its sum is never
truncated to a fixed number of frequencies or output degrees. -/
theorem current_complete_weighted_fourier_eventually (order : ℕ) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ hroom : 2 * order ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∀ coefficient : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order,
      weightedSupportEnergy Finset.univ
        (fun frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security) =>
          (FrequencySupport.support frequency).card)
        (fun frequency => ‖FourierCoordinates.fourier (ZMod.finEquiv (Parameters.modulus security)).toEquiv
          (fun word => (signedOutputMass security order hroom layout coefficient word : ℂ)) frequency‖ ^ 2)
        (BackgroundRates.radius security / Real.sqrt (Real.exp 1)) ≤
        (normConstant order 1 * coefficientNorm (primaryLaw security) (ActualControls.bodyReference security)
          order (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) coefficient) ^ 2 := by
  obtain ⟨threshold, hthreshold⟩ := current_signed_fock_eventually order
  refine ⟨threshold, ?_⟩
  intro security hsecurity hroom layout coefficient
  have hpop : 0 < Fintype.card (Fin (Parameters.dimension security)) := by
    rw [Fintype.card_fin]
    exact_mod_cast dimension_pos security
  have h := FourierSupportIsometry.complete_weighted_energy_le_fock
    (ZMod.finEquiv (Parameters.modulus security)).toEquiv
    (signedOutputMass security order hroom layout coefficient)
    (HistogramNormalization.symmetrizedMass_exchangeable _)
    hpop (BackgroundRates.radius security)
  exact h.trans (hthreshold security hsecurity hroom layout coefficient)

end

end CurrentAFT.ActualWeightedFourier

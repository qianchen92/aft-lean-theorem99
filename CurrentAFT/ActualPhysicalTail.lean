import CurrentAFT.ActualWeightedFourier
import CurrentAFT.SupportTail

/-!
# Full physical Fourier tail with the weighted-energy premise discharged

The remaining cancellation premise is the explicit finite collection of
linear Fourier constraints to be solved by calibration. The complete
physical weighted norm is supplied by the actual-law proof.
-/

namespace CurrentAFT.ActualPhysicalTail

open AFT DiffuseProfiles ProposalPrimary ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean PhysicalFockRates ControlCoordinates ControlNorm
  CoefficientOutputFock ActualWeightedFourier
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.dimension BackgroundRates.radius

def analysisRadius (security : ℕ) : ℝ := BackgroundRates.radius security / Real.sqrt (Real.exp 1)

def coefficient (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security)
    (input : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order)
    (frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)) : ℂ :=
  FourierCoordinates.fourier (ZMod.finEquiv (Parameters.modulus security)).toEquiv
    (fun word => (signedOutputMass security order hroom layout input word : ℂ)) frequency

theorem analysisRadius_eventually : ∃ threshold : ℕ, ∀ security ≥ threshold, 1 ≤ analysisRadius security := by
  refine ⟨Nat.ceil (Real.exp 1 ^ 2) + 1, ?_⟩
  intro security hsecurity
  have hbase : Real.exp 1 ^ 2 ≤ (Parameters.base security : ℝ) := by
    have hn : Nat.ceil (Real.exp 1 ^ 2) ≤ Parameters.base security := by rw [Parameters.base]; omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hroot : Real.exp 1 ≤ Real.sqrt (Parameters.base security : ℝ) := Real.le_sqrt_of_sq_le hbase
  have hradius : Real.sqrt (Real.exp 1) ≤ BackgroundRates.radius security := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨radius_nonneg security, ?_⟩
    rw [radius_square]
    exact hroot
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (Real.exp_pos 1))).mpr (by simpa only [one_mul] using hradius)

/-- Exact low-support calibration now implies a bound on the complete
remaining frequency sum of the actual physical output family. No weighted
norm, Fock estimate, or tail estimate is assumed. -/
theorem current_complete_tail_eventually (order : ℕ) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ hroom : 2 * order ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∀ input : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order,
      (∀ frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security),
        frequency ≠ 0 → (FrequencySupport.support frequency).card ≤ order →
          coefficient security order hroom layout input frequency = 0) →
      (∑ frequency ∈ Finset.univ.erase (0 : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)),
        ‖coefficient security order hroom layout input frequency‖ ^ 2) ≤
      (normConstant order 1 * coefficientNorm (primaryLaw security) (ActualControls.bodyReference security)
        order (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) input) ^ 2 /
          analysisRadius security ^ (2 * (order + 1)) := by
  obtain ⟨weightedThreshold, hweighted⟩ := current_complete_weighted_fourier_eventually order
  obtain ⟨radiusThreshold, hradius⟩ := analysisRadius_eventually
  refine ⟨max weightedThreshold radiusThreshold, ?_⟩
  intro security hsecurity hroom layout input hcancel
  have hr := hradius security ((Nat.le_max_right _ _).trans hsecurity)
  have hw := hweighted security ((Nat.le_max_left _ _).trans hsecurity) hroom layout input
  apply complete_support_tail_of_weighted_bound
    (Finset.univ.erase (0 : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)))
    (fun frequency => (FrequencySupport.support frequency).card)
    (fun frequency => ‖coefficient security order hroom layout input frequency‖ ^ 2)
    order (analysisRadius security) _ hr
    (fun _ _ => sq_nonneg _) (fun frequency hfrequency hsmall => by
      dsimp only
      rw [hcancel frequency (Finset.mem_erase.mp hfrequency).1 hsmall]
      norm_num)
  apply (show weightedSupportEnergy
      (Finset.univ.erase (0 : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)))
      (fun frequency => (FrequencySupport.support frequency).card)
      (fun frequency => ‖coefficient security order hroom layout input frequency‖ ^ 2) (analysisRadius security) ≤
    weightedSupportEnergy Finset.univ
      (fun frequency => (FrequencySupport.support frequency).card)
      (fun frequency => ‖coefficient security order hroom layout input frequency‖ ^ 2) (analysisRadius security) from
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ =>
      mul_nonneg (pow_nonneg (by linarith : 0 ≤ analysisRadius security) _) (sq_nonneg _))).trans
  exact hw

end

end CurrentAFT.ActualPhysicalTail

import AFT.ActualPairedFibers
import AFT.CanonicalJointInverse

/-! # Exact calibrated inputs for the actual connected paired coefficients -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter MixedKernel
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pairedInverseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pairedInverseSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- A literal joint input for the actual selected coefficient. It is obtained
by applying the finite calibrated inverse to each retained coordinate. -/
def actualJointPairedInverse (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ))
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (queue : ℤ)
    (profile : (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) → Fin (Parameters.modulus parameter) → ℝ)
    (selected : Finset (Fin 4)) : (selected → Fin (Parameters.modulus parameter)) → ℝ :=
  inverseJointKernel (fun _ : selected => actualPrimaryLaw cutoffScale parameter beta)
    (v7Activation cutoffScale parameter) operator
    (LocalTensors.restrictedComponent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter beta)
      (actualJointPairedNumerator cutoffScale parameter beta charts queue profile) selected)

/-- One genuine calibrated inverse provides exact canonical inputs for all
selected paired coefficients and all joint root/input profiles simultaneously.
The full mixed activity, including every fixed fiber, is bounded explicitly. -/
theorem actual_joint_paired_inverse_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter) :
    ∀ᶠ parameter in atTop,
    ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
    operator.toLinearMap = actualResponse cutoffScale parameter ∧
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ queue : ℤ, |queue| ≤ (queueCutoff parameter : ℤ) →
    ∀ profile : (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) → Fin (Parameters.modulus parameter) → ℝ,
      (∀ roots, (∑ color, profile roots color) = 0) →
    ∀ selected : Finset (Fin 4),
    (v7Activation cutoffScale parameter)^selected.card •
      inputIteration (allCoordinates (Slot := selected)).reverse (fun _ => operator.toLinearMap)
        (fun _ : selected => actualPrimaryLaw cutoffScale parameter (beta parameter))
        (actualJointPairedInverse cutoffScale parameter (beta parameter) operator charts queue profile selected) =
      LocalTensors.restrictedComponent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
        (actualJointPairedNumerator cutoffScale parameter (beta parameter) charts queue profile) selected ∧
    Hoeffding.Canonical (fun _ : selected => actualPrimaryLaw cutoffScale parameter (beta parameter)) Finset.univ
      (actualJointPairedInverse cutoffScale parameter (beta parameter) operator charts queue profile selected) ∧
    activity (fun _ : selected => 1 / Real.sqrt (pool parameter : ℝ))
      (fun _ : selected => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (actualJointPairedInverse cutoffScale parameter (beta parameter) operator charts queue profile selected) ≤
      (4 / v7Activation cutoffScale parameter)^selected.card *
      ((1 / Real.sqrt (pool parameter : ℝ))^selected.card *
        (1 + 2 * (1 / Real.sqrt (pool parameter : ℝ)) * Real.sqrt (Parameters.modulus parameter : ℝ))^selected.card *
        Real.sqrt ((26912768 * (parameter : ℝ)^8) *
          ∑ roots, (pairedRootReference parameter).weight roots *
            profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (profile roots))) := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_inverse_mixed_uniform_eventually cutoffScale hscale beta pool htypical,
    actual_joint_paired_component_activity_eventually cutoffScale hscale beta hbeta,
    actual_primary_law_quarter_lower_eventually cutoffScale hscale beta hbeta,
    actualResponse_inverse_mass_eventually cutoffScale hscale, eventually_ge_atTop 1]
    with parameter hi hc hp hm hparameter
  obtain ⟨operator,hop,hi⟩ := hi
  refine ⟨operator,hop,?_⟩
  intro charts hcharts queue hqueue profile hcanonical selected
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hpositive (color : Fin (Parameters.modulus parameter)) :
      0 < (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color :=
    (by positivity : (0 : ℝ) < 1 / (4 * (Parameters.modulus parameter : ℝ))).trans_le (hp color)
  have hrho : 0 < v7Activation cutoffScale parameter :=
    activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale hparameter)
  have hexact := inverseJointKernel_exact (fun _ : selected => actualPrimaryLaw cutoffScale parameter (beta parameter))
    (v7Activation cutoffScale parameter) hrho.ne' operator (fun _ color => (hpositive color).ne')
    (LocalTensors.restrictedComponent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (actualJointPairedNumerator cutoffScale parameter (beta parameter) charts queue profile) selected)
  simp only [Fintype.card_coe] at hexact
  refine ⟨hexact,?_,?_⟩
  · apply inverseJointKernel_canonical _ _ operator (fun _ color => (hpositive color).ne') (hm operator hop)
    exact LocalTensors.restrictedComponent_canonical _ (fun _ => hpositive) _ selected
  · have hinv := inverseJointKernel_activity_le
      (fun _ : selected => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (fun _ : selected => 1 / Real.sqrt (pool parameter : ℝ)) (v7Activation cutoffScale parameter) hrho operator
      (fun slot kernel => hi selected _ _ slot (fun _ => by positivity) rfl rfl kernel)
      (LocalTensors.restrictedComponent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
        (actualJointPairedNumerator cutoffScale parameter (beta parameter) charts queue profile) selected)
    simp only [Fintype.card_coe] at hinv
    exact hinv.trans (mul_le_mul_of_nonneg_left
      (hc charts hcharts queue hqueue profile hcanonical selected _ (by positivity))
      (pow_nonneg (div_nonneg (by norm_num) hrho.le) _))

end
end AFT.V7Calibration

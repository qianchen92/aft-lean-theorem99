import AFT.JointBoundaryAlgebra
import AFT.V7ActualProjection
import AFT.V7ReferenceLaws
import AFT.PrimarySeedCanonical
import AFT.ActualPairedInverse

/-! # The real calibrated joint boundary projection -/
namespace AFT.V7Calibration
open GaussianSource MixedKernel Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The exact all-primary joint projection formed from the actual response
inverse. It retains one whole boundary ideal, not the intersection of the
coordinatewise interior spaces. -/
def actualJointBoundaryProjection (C : ℝ) (n : ℕ) (beta : ℝ)
    {Slot : Type*} [Fintype Slot] [DecidableEq Slot] (coordinates : List Slot)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :
    Module.End ℝ ((Slot → Fin (Parameters.modulus n)) → ℝ) :=
  jointLegalProjection coordinates (fun _ => legalInputProjection operator
    (boundaryIdealProjection (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
      (GaussianSource.actualPrimary C beta n))) (fun _ => actualPrimaryLaw C n beta)

/-- Actual-source hypotheses discharge scalar legality and positivity.
All conditional boundary cells and arbitrary joint input kernels share the
same actual calibrated operator. -/
theorem actual_joint_boundary_projection_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n →
      ∀ (Slot : Type*) [Fintype Slot] [DecidableEq Slot],
      ∀ coordinates : List Slot, coordinates.Nodup →
      ∀ kernel : (Slot → Fin (Parameters.modulus n)) → ℝ,
      (Hoeffding.Canonical (fun _ : Slot => actualPrimaryLaw C n (beta n)) Finset.univ kernel →
        Hoeffding.Canonical (fun _ : Slot => actualPrimaryLaw C n (beta n)) Finset.univ
          (actualJointBoundaryProjection C n (beta n) coordinates operator kernel)) ∧
      (∀ record : Slot → Option (Fin (Parameters.modulus n)),
        ∀ hpos : ∀ slot, 0 < (actualPrimaryLaw C n (beta n)).eventMass (fun color =>
          FiniteDist.boundaryRecord (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ color = record slot),
        (FiniteDist.independent (fun slot => (actualPrimaryLaw C n (beta n)).condition (fun color =>
          FiniteDist.boundaryRecord (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ color = record slot)
          (hpos slot))).expectation
          (actualJointBoundaryProjection C n (beta n) coordinates operator kernel) = 0) := by
  filter_upwards [actual_safe_projection_eventually C hC beta hbeta,
    actual_primary_law_quarter_lower_eventually C hC beta hbeta] with n hlegal hp
  intro operator hop Slot instFintype instDecidable coordinates hnodup kernel
  have hpositive (color : Fin (Parameters.modulus n)) :
      (actualPrimaryLaw C n (beta n)).weight color ≠ 0 := by
    have hq : (0 : ℝ) < Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
    exact ne_of_gt ((by positivity : (0 : ℝ) < 1 / (4 * (Parameters.modulus n : ℝ))).trans_le (hp color))
  have hl := (hlegal operator hop).1
  constructor
  · intro hc
    exact jointLegalProjection_canonical coordinates _ (fun _ => hpositive) _
      (fun _ profile => (hl profile).1) kernel hc
  · intro record hpos
    exact jointLegalProjection_boundary_mean_zero coordinates hnodup _ _ (fun _ => hpositive) _
      (fun _ profile => hl profile) record hpos kernel

/-- The leading joint image is preserved whenever the actual assembled
image is already in the whole output boundary ideal. -/
theorem actualJointBoundaryProjection_preserves_output (C : ℝ) (n : ℕ) (beta : ℝ)
    {Slot : Type*} [Fintype Slot] [DecidableEq Slot] (coordinates : List Slot)
    (hnodup : coordinates.Nodup) (hcomplete : ∀ slot, slot ∈ coordinates)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hpositive : ∀ color, (actualPrimaryLaw C n beta).weight color ≠ 0)
    (kernel : (Slot → Fin (Parameters.modulus n)) → ℝ)
    (houtput : jointLegalProjection coordinates (fun _ =>
      boundaryIdealProjection (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ (GaussianSource.actualPrimary C beta n))
      (fun _ => actualPrimaryLaw C n beta)
      (inputIteration coordinates (fun _ => operator.toLinearMap) (fun _ => actualPrimaryLaw C n beta) kernel) =
      inputIteration coordinates (fun _ => operator.toLinearMap) (fun _ => actualPrimaryLaw C n beta) kernel) :
    inputIteration coordinates (fun _ => operator.toLinearMap) (fun _ => actualPrimaryLaw C n beta)
      (actualJointBoundaryProjection C n beta coordinates operator kernel) =
      inputIteration coordinates (fun _ => operator.toLinearMap) (fun _ => actualPrimaryLaw C n beta) kernel := by
  have he := jointLegalProjection_evaluation coordinates hnodup hcomplete
    (fun _ => actualPrimaryLaw C n beta) (fun _ => hpositive) (fun _ => operator)
    (fun _ => boundaryIdealProjection (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ (GaussianSource.actualPrimary C beta n))
  exact (LinearMap.congr_fun he kernel).trans houtput

end
end AFT.V7Calibration

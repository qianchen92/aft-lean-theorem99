import AFT.ActualJointPaired
import AFT.CanonicalFiberEnergy

/-! # Actual paired root/input canonical coefficients in the full mixed activity -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pairedFibersFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pairedFibersSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Every genuine canonical output component has all its fixed fibers,
including an arbitrary joint two-root/input tensor, bounded simultaneously. -/
theorem actual_joint_paired_component_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ queue : ℤ, |queue| ≤ (queueCutoff parameter : ℤ) →
    ∀ profile : (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) → Fin (Parameters.modulus parameter) → ℝ,
      (∀ roots, (∑ color, profile roots color) = 0) →
    ∀ (selected : Finset (Fin 4)) (rate : ℝ), 0 ≤ rate →
    MixedKernel.activity (fun _ : selected => rate)
      (fun _ : selected => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (LocalTensors.restrictedComponent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
        (actualJointPairedNumerator cutoffScale parameter (beta parameter) charts queue profile) selected) ≤
      rate ^ selected.card * (1 + 2 * rate * Real.sqrt (Parameters.modulus parameter : ℝ)) ^ selected.card *
        Real.sqrt ((26912768 * (parameter : ℝ) ^ 8) *
          ∑ roots, (pairedRootReference parameter).weight roots *
            profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (profile roots)) := by
  filter_upwards [actual_joint_paired_primary_energy_eventually cutoffScale hscale beta hbeta,
    actual_primary_law_quarter_lower_eventually cutoffScale hscale beta hbeta]
    with parameter he hp charts hc queue hqueue profile hcanonical selected rate hrate
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hlower : (0 : ℝ) < 1 / (4 * (Parameters.modulus parameter : ℝ)) := by positivity
  have hh := LocalTensors.restrictedComponent_activity_le
    (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
    (1 / (4 * (Parameters.modulus parameter : ℝ))) hlower (fun _ color => hp color)
    (actualJointPairedNumerator cutoffScale parameter (beta parameter) charts queue profile) selected rate hrate
  have hroot : Real.sqrt (1 / (4 * (Parameters.modulus parameter : ℝ))) =
      1 / (2 * Real.sqrt (Parameters.modulus parameter : ℝ)) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hcoef : 1 + rate / Real.sqrt (1 / (4 * (Parameters.modulus parameter : ℝ))) =
      1 + 2 * rate * Real.sqrt (Parameters.modulus parameter : ℝ) := by
    rw [hroot]
    field_simp
  rw [hcoef] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (he charts hc queue hqueue profile hcanonical))
  exact mul_nonneg (pow_nonneg hrate _) (pow_nonneg (by positivity) _)

end
end AFT.V7Calibration

import AFT.FixedPairedPrimaryEnergy
import AFT.JointSignedChannel

/-! # The genuine two-root/public-input joint paired numerator -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualJointPairedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The reference for the two physical roots of one selected paired block. -/
def pairedRootReference (parameter : ℕ) : FiniteDist (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) :=
  (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
    (Parameters.bodies_positive parameter)).prod
  (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
    (Parameters.bodies_positive parameter))

/-- The full joint source/input tensor is integrated once. There is no
factorization of its root dependence or its public primary argument. -/
def actualJointPairedNumerator (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (queue : ℤ)
    (profile : (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) → Fin (Parameters.modulus parameter) → ℝ)
    (word : Fin 4 → Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ roots, (pairedRootReference parameter).weight roots *
    fixedPairedChartRaw cutoffScale parameter beta charts roots.1 roots.2 queue (profile roots) word

/-- Uniform scalar bounds extend to the actual joint two-root/input
operator, with the norm of the entire joint tensor used only once. -/
theorem actual_joint_paired_primary_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
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
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).weight
      (actualJointPairedNumerator cutoffScale parameter (beta parameter) charts queue profile) ≤
    (26912768 * (parameter : ℝ) ^ 8) *
      ∑ roots, (pairedRootReference parameter).weight roots *
        profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (profile roots) := by
  filter_upwards [fixedPairedChartRaw_primary_energy_eventually cutoffScale hscale beta hbeta]
    with parameter he charts hc queue hqueue profile hp
  have hroot (roots : Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) :
      |(roots.1 : ℤ)| ≤ (v7RootCutoff parameter : ℤ) := abs_le.mpr (Finset.mem_Icc.mp roots.1.property)
  have hh := profileSquareNorm_average_le (pairedRootReference parameter)
    (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).weight
    (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).nonneg
    (fun roots => fixedPairedChartRaw cutoffScale parameter (beta parameter) charts roots.1 roots.2 queue (profile roots))
  apply hh.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro roots _
  exact (mul_le_mul_of_nonneg_left (he charts hc roots.1 roots.2 queue (hroot roots) hqueue (profile roots) (hp roots))
    ((pairedRootReference parameter).nonneg roots)).trans_eq (by ring)

end
end AFT.V7Calibration

import AFT.IndependentRootBlock
import AFT.RootCenteredPairedFirst

/-! # Exact leading response after averaging independent physical roots -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration PhysicalBlockTensors Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentFirstFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Averaging the actual compensator root gives exactly the marginal
anchor already used in the calibrated response. -/
theorem independent_root_anchor_average (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    (∑ roots, (pairedRootReference parameter).weight roots * integerAnchorShiftProfile parameter roots.2 profile output) =
      blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)) profile output.val := by
  simp only [pairedRootReference,Fintype.sum_prod_type,FiniteDist.prod_weight, mul_assoc,
    ← Finset.mul_sum,← Finset.sum_mul,FiniteDist.sum_one,one_mul]
  unfold integerAnchorShiftProfile integerAnchorProfile blurredAnchorMean blurredAnchorKernel
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro color _
  apply Finset.sum_congr rfl
  intro root _
  ring

/-- The independent-root leading count is exactly rho*A, while the full
physical signed numerator has zero total mass. -/
theorem independentPaired_first_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
      conditionalJointOutput cutoffScale parameter mark attached first second) ∧
    ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ color, profile color) = 0 →
    (∑ word, independentPairedNumerator cutoffScale parameter (beta parameter) charts profile word) = 0 ∧
    ∀ output, fourOutputCount (independentPairedNumerator cutoffScale parameter (beta parameter) charts profile) output =
      v7Activation cutoffScale parameter * actualResponse cutoffScale parameter profile output := by
  filter_upwards [fixed_paired_first_response_with_charts_eventually cutoffScale hscale beta hbeta,
    fixedPairedChartRaw_count_eventually cutoffScale hscale beta hbeta,
    fixedPairedChartRaw_mass_eventually cutoffScale hscale beta hbeta]
    with parameter hc hcount hmass
  obtain ⟨charts,hcharts,hformula⟩ := hc
  refine ⟨charts,hcharts,?_⟩
  intro profile hcanonical
  have hroot (root : Window (v7RootCutoff parameter)) : |(root : ℤ)| ≤ (v7RootCutoff parameter : ℤ) :=
    abs_le.mpr (Finset.mem_Icc.mp root.property)
  constructor
  · unfold independentPairedNumerator actualJointPairedNumerator
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,hmass charts _ _ 0 (hroot _) profile hcanonical,mul_zero,Finset.sum_const_zero]
  · intro output
    unfold independentPairedNumerator actualJointPairedNumerator
    rw [fourOutputCount_sum]
    simp_rw [fourOutputCount_smul]
    simp_rw [hcount charts _ _ 0 (hroot _) profile hcanonical output,
      hformula profile hcanonical _ output]
    simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hfactor (function : (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) → ℝ) :
        (∑ roots, (pairedRootReference parameter).weight roots * (v7Activation cutoffScale parameter * function roots)) =
          v7Activation cutoffScale parameter * ∑ roots, (pairedRootReference parameter).weight roots * function roots := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro roots _
      ring
    simp_rw [hfactor]
    rw [independent_root_anchor_average]
    simp only [← Finset.sum_mul,FiniteDist.sum_one,one_mul]
    ring

end
end AFT.V7Calibration

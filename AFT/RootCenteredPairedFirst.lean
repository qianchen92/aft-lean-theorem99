import AFT.ActualJointPaired
import AFT.RootAnchorResponse

/-! # Exact centered-root cancellation in the actual paired first response -/

namespace AFT
open scoped BigOperators Classical
noncomputable section
variable {Source Color Output : Type*} [Fintype Source] [Fintype Color]

omit [Fintype Color] in
theorem weighted_linear_mean_zero (law : FiniteDist Source)
    (operator : (Color → ℝ) →ₗ[ℝ] (Output → ℝ)) (profiles : Source → Color → ℝ)
    (hmean : ∀ color, (∑ source, law.weight source * profiles source color) = 0)
    (output : Output) : (∑ source, law.weight source * operator (profiles source) output) = 0 := by
  have hz : (∑ source, law.weight source • profiles source) = 0 := by
    funext color
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hmean color
  have hh := congrArg (fun profile => operator profile output) hz
  simpa only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,map_zero,Pi.zero_apply] using hh

theorem weighted_matrix_mean_zero (law : FiniteDist Source)
    (matrix : Color → ℝ) (profiles : Source → Color → ℝ)
    (hmean : ∀ color, (∑ source, law.weight source * profiles source color) = 0) :
    (∑ source, law.weight source * ∑ color, profiles source color * matrix color) = 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro color _
  simp only [← mul_assoc,← Finset.sum_mul,hmean,zero_mul]

/-- Integrate the attachment coordinate before applying a channel which
only depends on the compensator root. -/
theorem product_root_matrix_mean_zero (first second : FiniteDist Source)
    (matrix : Source → Color → ℝ) (profiles : Source × Source → Color → ℝ)
    (hmean : ∀ right color, (∑ left, first.weight left * profiles (left,right) color) = 0) :
    (∑ roots, (first.prod second).weight roots * ∑ color, profiles roots color * matrix roots.2 color) = 0 := by
  simp only [Fintype.sum_prod_type,FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro right _
  calc
    _ = second.weight right * ∑ left, first.weight left * ∑ color, profiles (left,right) color * matrix right color := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro left _
      ring
    _ = 0 := by rw [weighted_matrix_mean_zero first _ _ (hmean right),mul_zero]

omit [Fintype Color] in
theorem product_root_profile_mean_zero (first second : FiniteDist Source)
    (profiles : Source × Source → Color → ℝ)
    (hmean : ∀ right color, (∑ left, first.weight left * profiles (left,right) color) = 0) :
    ∀ color, (∑ roots, (first.prod second).weight roots * profiles roots color) = 0 := by
  intro color
  simp only [Fintype.sum_prod_type,FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro right _
  calc
    _ = second.weight right * ∑ left, first.weight left * profiles (left,right) color := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro left _
      ring
    _ = 0 := by rw [hmean,mul_zero]

end
end AFT

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration PhysicalBlockTensors Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootCenteredPairedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- On an arbitrary jointly centered root/input profile, the actual full
first count is exactly the compensating translated-anchor difference. -/
theorem actual_joint_paired_centered_first_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
        conditionalJointOutput cutoffScale parameter mark attached first second) ∧
      ∀ queue : ℤ,
      ∀ profile : (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) → Fin (Parameters.modulus parameter) → ℝ,
      (∀ roots, (∑ color, profile roots color) = 0) →
      (∀ color, (∑ roots, (pairedRootReference parameter).weight roots * profile roots color) = 0) →
      ∀ output,
      fourOutputCount (actualJointPairedNumerator cutoffScale parameter (beta parameter) charts queue profile) output =
        -(v7Activation cutoffScale parameter) * ∑ roots, (pairedRootReference parameter).weight roots *
          integerAnchorDifferenceProfile parameter roots.2 (profile roots) output := by
  filter_upwards [fixed_paired_first_response_with_charts_eventually cutoffScale hscale beta hbeta,
    fixedPairedChartRaw_count_eventually cutoffScale hscale beta hbeta]
    with parameter hc hcount
  obtain ⟨charts,hcharts,hformula⟩ := hc
  refine ⟨charts,hcharts,?_⟩
  intro queue profile hcanonical hmean output
  have hcroot (root : Window (v7RootCutoff parameter)) : |(root : ℤ)| ≤ (v7RootCutoff parameter : ℤ) :=
    abs_le.mpr (Finset.mem_Icc.mp root.property)
  have hfirst : (∑ roots, (pairedRootReference parameter).weight roots *
      actualResponse cutoffScale parameter (profile roots) output) = 0 :=
    weighted_linear_mean_zero _ _ profile hmean output
  have havg : (∑ roots, (pairedRootReference parameter).weight roots *
      blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)) (profile roots) output.val) = 0 :=
    weighted_matrix_mean_zero _ _ profile hmean
  have hzero : (∑ roots, (pairedRootReference parameter).weight roots *
      integerAnchorShiftProfile parameter 0 (profile roots) output) = 0 :=
    weighted_matrix_mean_zero _ _ profile hmean
  unfold actualJointPairedNumerator
  rw [fourOutputCount_sum]
  simp_rw [fourOutputCount_smul]
  simp_rw [hcount charts _ _ queue (hcroot _) _ (hcanonical _) output,
    hformula _ (hcanonical _) _ output]
  simp only [integerAnchorDifferenceProfile,Pi.sub_apply,mul_add,mul_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hfactor (function : (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) → ℝ) :
      (∑ roots, (pairedRootReference parameter).weight roots * (v7Activation cutoffScale parameter * function roots)) =
        v7Activation cutoffScale parameter * ∑ roots, (pairedRootReference parameter).weight roots * function roots := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro roots _
    ring
  simp_rw [hfactor]
  rw [hfirst,havg,hzero]
  ring

/-- If the attached root is centered as well, the complete first count
vanishes exactly. Both roots remain in one joint tensor throughout. -/
theorem actual_joint_paired_two_root_first_zero_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
        conditionalJointOutput cutoffScale parameter mark attached first second) ∧
      ∀ queue : ℤ,
      ∀ profile : (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) → Fin (Parameters.modulus parameter) → ℝ,
      (∀ roots, (∑ color, profile roots color) = 0) →
      (∀ right color, (∑ left, (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter)
        (Parameters.bodies parameter) (Parameters.bodies_positive parameter)).weight left * profile (left,right) color) = 0) →
      ∀ output,
      fourOutputCount (actualJointPairedNumerator cutoffScale parameter (beta parameter) charts queue profile) output = 0 := by
  filter_upwards [actual_joint_paired_centered_first_eventually cutoffScale hscale beta hbeta] with parameter hc
  obtain ⟨charts,hcharts,hfirst⟩ := hc
  refine ⟨charts,hcharts,?_⟩
  intro queue profile hcanonical hroot output
  have hmean := product_root_profile_mean_zero
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter) (Parameters.bodies_positive parameter))
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter) (Parameters.bodies_positive parameter))
    profile hroot
  rw [hfirst queue profile hcanonical hmean output]
  have hshift (shift : Window (v7RootCutoff parameter) → ℤ) :
      (∑ roots, (pairedRootReference parameter).weight roots *
        integerAnchorShiftProfile parameter (shift roots.2) (profile roots) output) = 0 :=
    product_root_matrix_mean_zero _ _
      (fun root color => publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        color ((output.val : ℤ) - shift root)) profile hroot
  simp only [integerAnchorDifferenceProfile,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
  rw [hshift (fun root => (root : ℤ)),hshift (fun _ => 0),sub_self]

end
end AFT.V7Calibration

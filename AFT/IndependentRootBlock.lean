import AFT.ActualIndependentPairedBounds
import AFT.ActualJointPaired
import AFT.MixedAveraging

/-! # The literal independent-root, queue-free controlled paired block -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration PhysicalBlockTensors Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentRootBlockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Controlled attachments and their matched compensators have zero queue
shift. Both roots are averaged under the actual independent marginal law. -/
def independentPairedNumerator (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (profile : Fin (Parameters.modulus parameter) → ℝ) :
    (Fin 4 → Fin (Parameters.modulus parameter)) → ℝ :=
  actualJointPairedNumerator cutoffScale parameter beta charts 0 (fun _ => profile)

def independentPairedDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (profile : Fin (Parameters.modulus parameter) → ℝ)
    (word : Fin 4 → Fin (Parameters.modulus parameter)) : ℝ :=
  independentPairedNumerator cutoffScale parameter beta charts profile word /
    (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter beta)).weight word

theorem independentPairedDensity_average (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (word) :
    independentPairedDensity cutoffScale parameter beta charts profile word =
      ∑ roots, (pairedRootReference parameter).weight roots *
        fixedPairedPrimaryDensity cutoffScale parameter beta charts roots.1 roots.2 0 profile word := by
  simp only [independentPairedDensity, independentPairedNumerator, actualJointPairedNumerator,
    fixedPairedPrimaryDensity, Finset.sum_div, mul_div_assoc]

/-- Complete sharp scalar fibers after averaging the two actual marginal
roots. The upper response never invokes a connected-root allocation here. -/
theorem independentPairedDensity_fibers_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ color, profile color) = 0 →
    ∀ bound : ℝ, 0 ≤ bound →
      (∀ color, |profile color / (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color| ≤ bound) →
    (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).l2Sq
        (independentPairedDensity cutoffScale parameter (beta parameter) charts profile) ≤
        (26912768 * (parameter : ℝ) ^ 8) * profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile ∧
    (∀ slot values, MixedKernel.fiberSq (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (independentPairedDensity cutoffScale parameter (beta parameter) charts profile)
      {slot} values ≤ (34816 * 2048 * 773 ^ 2) * (parameter : ℝ) ^ 8 * bound ^ 2) ∧
    (∀ word, |independentPairedDensity cutoffScale parameter (beta parameter) charts profile word| ≤
      (34816 * 773) * (parameter : ℝ) ^ 8 * bound) := by
  filter_upwards [fixedPairedPrimaryDensity_fibers_eventually cutoffScale hscale beta hbeta]
    with parameter h charts hc profile hcanonical bound hbound hprofile
  have hr (root : Window (v7RootCutoff parameter)) : |(root : ℤ)| ≤ (v7RootCutoff parameter : ℤ) :=
    abs_le.mpr (Finset.mem_Icc.mp root.property)
  have hh (roots : Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) :=
    h charts hc roots.1 roots.2 0 (hr roots.1) (hr roots.2) (by simp) profile hcanonical bound hbound hprofile
  have heq : independentPairedDensity cutoffScale parameter (beta parameter) charts profile =
      fun word => ∑ roots, (pairedRootReference parameter).weight roots *
        fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts roots.1 roots.2 0 profile word :=
    funext (independentPairedDensity_average _ _ _ _ _)
  rw [heq]
  refine ⟨?_,?_,?_⟩
  · exact FiniteDist.l2Sq_average_le_bound (pairedRootReference parameter) _ _ _ (fun roots => (hh roots).1)
  · intro slot values
    exact MixedKernel.fiberSq_average_le_bound (pairedRootReference parameter) _ _ _ _ _
      (fun roots => (hh roots).2.1 slot values)
  · intro word
    exact FiniteDist.abs_average_le_bound (pairedRootReference parameter) _ _ (fun roots => (hh roots).2.2 word)

/-- The positive local factor uses the same actual roots and original
unweighted primary/compensator distribution as the selected numerator. -/
def independentPairedPositiveMass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (word : Fin 4 → Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ roots, (pairedRootReference parameter).weight roots *
    ∑ input, ((actualPrimaryLaw cutoffScale parameter beta).prod (actualBodyLaw cutoffScale parameter beta)).weight input *
      fixedPairedKernel cutoffScale parameter beta charts roots.1 roots.2 0 input word

/-- The literal local denominator is a probability mass, not a formal
normalizing coefficient supplied as a hypothesis. -/
theorem independentPairedPositiveMass_probability_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ word, 0 ≤ independentPairedPositiveMass cutoffScale parameter (beta parameter) charts word) ∧
    (∑ word, independentPairedPositiveMass cutoffScale parameter (beta parameter) charts word) = 1 := by
  filter_upwards [fixed_compensator_masses_eventually cutoffScale hscale beta hbeta]
    with parameter hm charts
  constructor
  · intro word
    exact Finset.sum_nonneg fun roots _ => mul_nonneg (FiniteDist.nonneg _ _)
      (Finset.sum_nonneg fun input _ => mul_nonneg (FiniteDist.nonneg _ _)
        (fixedPairedKernel_nonneg _ _ _ _ _ _ _ _ _))
  · have hroot (roots : Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) :
        (∑ word, ∑ input,
          ((actualPrimaryLaw cutoffScale parameter (beta parameter)).prod (actualBodyLaw cutoffScale parameter (beta parameter))).weight input *
            fixedPairedKernel cutoffScale parameter (beta parameter) charts roots.1 roots.2 0 input word) = 1 := by
      simp_rw [fixedPairedKernel_average_factor]
      change (∑ word : Fin 4 → Fin (Parameters.modulus parameter),
        signedChartTriple cutoffScale parameter (beta parameter) charts roots.1 0
          (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word 0) (word 1) (word 2) *
          integerShiftProfile parameter (actualBodyLaw cutoffScale parameter (beta parameter)).weight roots.2 (word 3)) = 1
      rw [four_output_product_mass_instance, signedChartTriple_total,
        (actualPrimaryLaw cutoffScale parameter (beta parameter)).sum_one,
        (hm roots.2 (abs_le.mpr (Finset.mem_Icc.mp roots.2.property))).1, one_mul]
    unfold independentPairedPositiveMass
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hroot, mul_one, FiniteDist.sum_one]

end
end AFT.V7Calibration

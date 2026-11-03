import AFT.ActualConditionalJointProgram
import AFT.FixedPairedKernel

/-! # Executable actual four-output channel at fixed roots -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- Only finite rational kernels and integer equalities are evaluated.
The positive chart family is eliminated by its proved response identity. -/
def fixedPairedKernelProgram (constant n : ℕ) (beta : ℚ)
    (attachedRoot compensatorRoot queue : ℤ) (mark center : ℕ) (word : Fin 4 → ℕ) : ℚ :=
  probabilityClamp ((conditionalJointProgram constant n mark
    (fun source => probabilityClamp (actualShiftedBodyProgram constant n beta (attachedRoot+source+queue) (word 2)))
      (word 0) (word 1))*(if (word 3 : ℤ)=(center : ℤ)+compensatorRoot then 1 else 0))

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
local instance fixedPairedProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def fixedPairedKernelProgramError (n : ℕ) : ℝ := conditionalJointProgramError n+3*actualShiftedBodyProgramError n

theorem fixedPairedKernelProgramError_negligible : Negligible fixedPairedKernelProgramError := by
  exact conditionalJointProgramError_negligible.add (actualShiftedBodyProgramError_negligible.const_mul 3)

theorem fixedPairedKernel_le_one (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (attachedRoot compensatorRoot queue : ℤ) (input word) :
    fixedPairedKernel C n beta charts attachedRoot compensatorRoot queue input word ≤ 1 :=
  (Finset.single_le_sum (fun other (_ : other∈Finset.univ) =>
    fixedPairedKernel_nonneg C n beta charts attachedRoot compensatorRoot queue input other)
    (Finset.mem_univ word)).trans (fixedPairedKernel_mass_le C n beta charts attachedRoot compensatorRoot queue input)

/-- All auxiliary distributions and all response entries in the rational
program are instantiated with the actual model. -/
theorem fixed_paired_kernel_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily constant n mark,
    (∀ mark attached first second,publicChartRaw constant n mark (charts mark) attached first second=
      conditionalJointOutput constant n mark attached first second) →
    ∀ (attachedRoot compensatorRoot queue : ℤ), |attachedRoot| ≤ (v7RootCutoff n : ℤ) →
      |queue| ≤ (queueCutoff n : ℤ) →
    ∀ (input : Fin (Parameters.modulus n) × Fin (Parameters.modulus n))
      (word : Fin 4 → Fin (Parameters.modulus n)),
      |(fixedPairedKernelProgram constant n (beta n) attachedRoot compensatorRoot queue input.1.val input.2.val
          (fun slot => (word slot).val) : ℝ)-
        fixedPairedKernel constant n (beta n) charts attachedRoot compensatorRoot queue input word| ≤
          fixedPairedKernelProgramError n := by
  filter_upwards [conditional_joint_program_eventually constant hc,
    actual_shifted_body_clamp_program_eventually constant hc beta hbeta] with n htriple hbody
  intro charts hcharts attachedRoot compensatorRoot queue hroot hqueue input word
  let actualAttached := fun source : ℤ =>
    (actualShiftedBodyLaw constant n (beta n) (attachedRoot+source+queue)).weight (word 2)
  let approximateAttached := fun source : ℤ =>
    probabilityClamp (actualShiftedBodyProgram constant n (beta n) (attachedRoot+source+queue) (word 2).val)
  have hat (source : ℤ) : |actualAttached source| ≤ 1 := by
    rw [abs_of_nonneg (FiniteDist.nonneg _ _)]
    exact FiniteDist.atom_le_one _ _
  have hap (source : ℤ) : |(approximateAttached source : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (probabilityClamp_bounds _).1]
    exact (probabilityClamp_bounds _).2
  have hae (source : Window (actualLegCutoffProgram constant n-1)) :
      |(approximateAttached source : ℝ)-actualAttached source| ≤ actualShiftedBodyProgramError n := by
    apply hbody _ _
    have hh := actualBodyBranch_shift_bound (constant : ℝ) n attachedRoot queue hroot hqueue
      (Sum.inr (actualLegWindowEquiv constant n source))
    exact hh
  have he := htriple input.1 (word 0) (word 1) actualAttached approximateAttached
    (actualShiftedBodyProgramError n) hat hap hae
  have he0 : 0 ≤ fixedPairedKernelProgramError n := (abs_nonneg _).trans he
  apply (probabilityClamp_error _ _ (fixedPairedKernel_nonneg _ _ _ _ _ _ _ _ _)
    (fixedPairedKernel_le_one _ _ _ _ _ _ _ _ _)).trans
  simp only [fixedPairedKernel,Rat.cast_mul,apply_ite,Rat.cast_one,Rat.cast_zero,hcharts]
  split_ifs
  · simpa only [mul_one] using he
  · simpa only [mul_zero,sub_self,abs_zero] using he0

end
end AFT.V7Calibration

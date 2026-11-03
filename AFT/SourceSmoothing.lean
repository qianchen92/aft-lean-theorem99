import AFT.CompactSmoothing
import AFT.Correction

/-! # Finite source convolution and its actual compact-smoothing defect -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G σ : Type*} [Fintype G] [AddCommGroup G] [Fintype σ]

/-- The kernel of the source pushforward acts by averaging its true shifts. -/
theorem convolution_map_apply (source : FiniteDist σ) (shift : σ → G)
    (profile : G → ℝ) (output : G) :
    convolution (source.map shift).weight profile output =
      ∑ sample, source.weight sample * profile (output - shift sample) := by
  classical
  simp only [convolution_apply, FiniteDist.map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The full signed source defect is bounded before taking any norm of the
input, by averaging the exact finite translations. -/
theorem source_defect_L1_le (source : FiniteDist σ) (shift : σ → G)
    (profile : G → ℝ) :
    kernelL1 (profile - convolution (source.map shift).weight profile) ≤
      ∑ sample, source.weight sample * kernelL1 (fun color => profile color - profile (color - shift sample)) := by
  have heq (color : G) : (profile - convolution (source.map shift).weight profile) color =
      ∑ sample, source.weight sample * (profile color - profile (color - shift sample)) := by
    simp only [Pi.sub_apply, convolution_map_apply, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, source.sum_one, one_mul]
  unfold kernelL1
  simp_rw [heq]
  calc
    _ ≤ ∑ color : G, ∑ sample, |source.weight sample * (profile color - profile (color - shift sample))| :=
      Finset.sum_le_sum fun color _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [abs_mul, abs_of_nonneg (source.nonneg _), Finset.mul_sum]

variable [DecidableEq G]

/-- The genuine product of two compact integer interval kernels. -/
noncomputable def boxDistribution (embedding : ℤ →+ G) (start : ℤ) (width : ℕ) (hw : width ≠ 0) :
    FiniteDist (G × G) :=
  (intervalDistribution embedding start width hw).prod (intervalDistribution embedding start width hw)

/-- Independent or correlated source coordinates both satisfy the same
palette-independent box defect bound. -/
theorem box_source_defect_L1_le (embedding : ℤ →+ G) (start : ℤ) (width : ℕ) (hw : width ≠ 0)
    (source : FiniteDist σ) (firstShift secondShift : σ → ℤ) (shiftBound : ℝ)
    (hshift : ∀ sample, (firstShift sample).natAbs + (secondShift sample).natAbs ≤ shiftBound) :
    kernelL1 ((boxDistribution embedding start width hw).weight -
      convolution (source.map (fun sample => (embedding (firstShift sample), embedding (secondShift sample)))).weight
        (boxDistribution embedding start width hw).weight) ≤ 2 * shiftBound / width := by
  have hlocal (sample : σ) : kernelL1 (fun color : G × G =>
      (boxDistribution embedding start width hw).weight color -
      (boxDistribution embedding start width hw).weight
        (color - (embedding (firstShift sample), embedding (secondShift sample)))) ≤ 2 * shiftBound / width := by
    have hh := box_translation_L1_le embedding start (firstShift sample) (secondShift sample) width hw
    have heq : kernelL1 (fun color : G × G =>
        (boxDistribution embedding start width hw).weight color -
        (boxDistribution embedding start width hw).weight
          (color - (embedding (firstShift sample), embedding (secondShift sample)))) =
        kernelL1 (fun color : G × G =>
          intervalKernel embedding start width (color.1 - embedding (firstShift sample)) *
          intervalKernel embedding start width (color.2 - embedding (secondShift sample)) -
          intervalKernel embedding start width color.1 * intervalKernel embedding start width color.2) := by
      unfold kernelL1
      apply Finset.sum_congr rfl
      intro color _
      exact abs_sub_comm _ _
    rw [heq]
    exact hh.trans (div_le_div_of_nonneg_right (by linarith [hshift sample]) (Nat.cast_nonneg width))
  exact (source_defect_L1_le source
    (fun sample => (embedding (firstShift sample), embedding (secondShift sample))) _).trans (by
    calc
      _ ≤ ∑ sample, source.weight sample * (2 * shiftBound / width) :=
        Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (hlocal sample) (source.nonneg sample)
      _ = _ := by rw [← Finset.sum_mul, source.sum_one, one_mul])

/-- Actual root convolution after the compact box has small Hilbert norm.
The operator is formed from the finite source distribution itself. -/
theorem box_source_defect_L2_le (embedding : ℤ →+ G) (start : ℤ) (width : ℕ) (hw : width ≠ 0)
    (source : FiniteDist σ) (firstShift secondShift : σ → ℤ) (shiftBound : ℝ)
    (hshift : ∀ sample, (firstShift sample).natAbs + (secondShift sample).natAbs ≤ shiftBound)
    (profile : G × G → ℝ) :
    let R := convolution (source.map (fun sample => (embedding (firstShift sample), embedding (secondShift sample)))).weight
    let S := convolution (boxDistribution embedding start width hw).weight
    countingL2 (((1 - R) * S) profile) ≤ (2 * shiftBound / width) * countingL2 profile := by
  dsimp only
  have heq : (1 - convolution (source.map (fun sample => (embedding (firstShift sample), embedding (secondShift sample)))).weight) *
      convolution (boxDistribution embedding start width hw).weight =
      convolution ((boxDistribution embedding start width hw).weight -
        convolution (source.map (fun sample => (embedding (firstShift sample), embedding (secondShift sample)))).weight
          (boxDistribution embedding start width hw).weight) := by
    rw [convolution_sub_kernel, convolution_convolution, sub_mul, one_mul]
  rw [heq]
  exact (convolution_L2_le _ profile).trans (mul_le_mul_of_nonneg_right
    (box_source_defect_L1_le embedding start width hw source firstShift secondShift shiftBound hshift)
    (countingL2_nonneg profile))

end AFT.SafeConvolution

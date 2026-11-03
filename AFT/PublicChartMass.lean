import AFT.PublicChartGaussian

/-! # The true attached marginal is independent of the primary mark -/

namespace AFT

open scoped BigOperators Classical
noncomputable section

theorem sum_pair_mixture {Index Color : Type*} [Fintype Index] [Fintype Color]
    (weight : Index → ℝ) (kernel : Index → Color → Color → ℝ) :
    (∑ first, ∑ second, ∑ sample, weight sample * kernel sample first second) =
      ∑ sample, weight sample * ∑ first, ∑ second, kernel sample first second := by
  simp only [Finset.mul_sum]
  calc
    _ = ∑ first, ∑ sample, ∑ second, weight sample * kernel sample first second := by
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

namespace V7Calibration

open GaussianSource BoundaryCalibration
set_option backward.isDefEq.respectTransparency false
local instance chartMassFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The complete positive chart sampler has the exact second-source body
marginal, independently of the primary mark and selected affine charts. -/
theorem publicChartRaw_total (cutoffScale : ℝ) (parameter : ℕ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ) :
    (∑ first, ∑ second, publicChartRaw cutoffScale parameter mark charts attached first second) =
      ∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source * attached source := by
  have hinput (sample : bodySample cutoffScale parameter × Bool)
      (offset : PublicOffsets cutoffScale parameter mark sample) :
      (∑ first, ∑ second, ∑ input, (protectedGaussianLaw cutoffScale parameter).weight input *
        (chartPairOutput cutoffScale parameter offset (charts sample offset) input).weight (first,second) * attached input.2) =
      ∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source * attached source := by
    have heq (input) (first second) : (protectedGaussianLaw cutoffScale parameter).weight input *
        (chartPairOutput cutoffScale parameter offset (charts sample offset) input).weight (first,second) * attached input.2 =
        (protectedGaussianLaw cutoffScale parameter).weight input *
          ((chartPairOutput cutoffScale parameter offset (charts sample offset) input).weight (first,second) * attached input.2) := by ring
    simp only [heq]
    rw [sum_pair_mixture]
    have hm (input) : (∑ first, ∑ second,
        (chartPairOutput cutoffScale parameter offset (charts sample offset) input).weight (first,second)) = 1 := by
      simpa only [Fintype.sum_prod_type] using (chartPairOutput cutoffScale parameter offset (charts sample offset) input).sum_one
    simp only [← Finset.sum_mul, hm, one_mul, protectedGaussianLaw,
      Fintype.sum_prod_type, FiniteDist.prod_weight, mul_assoc, ← Finset.mul_sum,
      ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  have hsample (sample : bodySample cutoffScale parameter × Bool) :
      (∑ first, ∑ second, ∑ offset, (publicOffsetLaw cutoffScale parameter mark sample).weight offset *
        ∑ input, (protectedGaussianLaw cutoffScale parameter).weight input *
          (chartPairOutput cutoffScale parameter offset (charts sample offset) input).weight (first,second) * attached input.2) =
      ∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source * attached source := by
    rw [sum_pair_mixture]
    simp only [hinput, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  unfold publicChartRaw
  rw [sum_pair_mixture]
  simp only [hsample, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

/-- Hence a canonical primary score contributes zero to the attached
body's first coefficient for every realized root and shared queue. -/
theorem publicChartRaw_attached_canonical (cutoffScale : ℝ) (parameter : ℕ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (hcanonical : ∑ mark, profile mark = 0)
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ) :
    (∑ mark, profile mark * ∑ first, ∑ second,
      publicChartRaw cutoffScale parameter mark (charts mark) attached first second) = 0 := by
  simp only [publicChartRaw_total, ← Finset.sum_mul, hcanonical, zero_mul]

end V7Calibration
end
end AFT

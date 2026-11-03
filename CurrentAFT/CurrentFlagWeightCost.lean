import CurrentAFT.CurrentFlagWeightArray

/-! Costs and heights of the materialized branch probability arrays. -/

namespace CurrentAFT.CurrentFlagWeightArray

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagPublicProgram CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 400000

def regularWeightHeight (cutoff modulus steps : ℕ) : ℕ :=
  CurrentFlagBinary.iterateHeight (modulus * (modulus * modulus)) modulus
    ((2 * cutoff + 1) * (2 * cutoff + 1)) 1 steps + modulus * (modulus * modulus)

def regularWeightWork (cutoff modulus baselineBits steps : ℕ) : ℕ :=
  CurrentFlagPublicProgram.workBound cutoff modulus baselineBits steps +
    scaleWork (modulus * (modulus * modulus))
      (CurrentFlagBinary.iterateHeight (modulus * (modulus * modulus)) modulus
        ((2 * cutoff + 1) * (2 * cutoff + 1)) 1 steps) + 2

theorem regularWeights_height (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) (steps : ℕ)
    (point : Fin (modulus * (modulus * modulus))) :
    HeightBound ((regularWeights cutoff modulus baselineSign baseline mark steps).data.get point).decode
      (regularWeightHeight cutoff modulus steps) := by
  simp only [regularWeights, scale_value]
  exact (evaluate_height cutoff modulus baselineSign baseline mark steps point).div
    (HeightBound.nat_coarse (modulus * (modulus * modulus)))

theorem regularWeights_work (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) (steps : ℕ) :
    (regularWeights cutoff modulus baselineSign baseline mark steps).work ≤
      regularWeightWork cutoff modulus baseline.length steps := by
  let raw := CurrentFlagPublicProgram.evaluate cutoff modulus baselineSign baseline mark steps
  let H := CurrentFlagBinary.iterateHeight (modulus * (modulus * modulus)) modulus
    ((2 * cutoff + 1) * (2 * cutoff + 1)) 1 steps
  have he := evaluate_work cutoff modulus baselineSign baseline mark steps
  have hs := scale_work raw.data H (evaluate_height cutoff modulus baselineSign baseline mark steps)
  change (scale raw.data).work ≤ scaleWork (modulus * (modulus * modulus))
    (CurrentFlagBinary.iterateHeight (modulus * (modulus * modulus)) modulus
      ((2 * cutoff + 1) * (2 * cutoff + 1)) 1 steps) at hs
  change raw.work ≤ _ at he
  change raw.work + (scale raw.data).work + 2 ≤ _
  unfold regularWeightWork
  omega

def markedWeightWork (cutoff modulus baselineBits : ℕ) : ℕ :=
  let charts := modulus * (modulus * modulus)
  CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baselineBits +
    (charts * (spikeWork charts + 2) + 2) + scaleWork charts (2 * charts) + 3

theorem markedWeights_height (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus)
    (point : Fin (modulus * (modulus * modulus))) :
    HeightBound ((markedWeights cutoff modulus baselineSign baseline mark).data.get point).decode
      (3 * (modulus * (modulus * modulus))) := by
  simp only [markedWeights, scale_value, buildArray_get, chartSpike_value]
  have hh := (chartSpikeProgram_height (modulus * (modulus * modulus))
    (maskSet (build cutoff modulus false baselineSign [true] baseline mark).value.fiber) point).div
      (HeightBound.nat_coarse (modulus * (modulus * modulus)))
  convert hh using 1
  omega

theorem markedWeights_work (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) :
    (markedWeights cutoff modulus baselineSign baseline mark).work ≤ markedWeightWork cutoff modulus baseline.length := by
  let N := modulus * (modulus * modulus)
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let density := buildArray N (chartSpike metadata.value.fiber)
  have hm := build_work cutoff modulus false baselineSign [true] baseline mark
  have hd := buildArray_work N (spikeWork N) _ (chartSpike_work metadata.value.fiber)
  have hh (point : Fin N) : HeightBound (density.data.get point).decode (2 * N) := by
    dsimp [density]
    rw [buildArray_get, chartSpike_value]
    exact chartSpikeProgram_height N _ point
  have hs := scale_work density.data (2 * N) hh
  change metadata.work ≤ CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baseline.length at hm
  change density.work ≤ _ at hd
  change metadata.work + density.work + (scale density.data).work + 3 ≤ _
  change _ ≤ CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baseline.length +
    (N * (spikeWork N + 2) + 2) + scaleWork N (2 * N) + 3
  omega

end CurrentAFT.CurrentFlagWeightArray

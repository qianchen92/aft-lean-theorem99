import CurrentAFT.CurrentFlagDraw
import CurrentAFT.CurrentFlagReferenceSupport
import CurrentAFT.CurrentFlagWeightCost

/-! The two actual public flag branches, sampled with finite fair bits. -/

namespace CurrentAFT.CurrentFlagBranchDraw

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentFlagBinaryMetadata CurrentFlagWeightArray
open scoped BigOperators
set_option maxHeartbeats 500000

def regular (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ)
    (word : Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2) :
    CountedValue (Fin (modulus * (modulus * modulus))) :=
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let weights := regularWeights cutoff modulus baselineSign baseline mark (CurrentFlagTargetNorm.precisionSteps cutoff precisionBits)
  let result := CurrentFlagDraw.draw weights.data metadata.value.safe drawBits word
  ⟨result.value, metadata.work + weights.work + result.work + 3⟩

def marked (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (drawBits : ℕ)
    (word : Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2) :
    CountedValue (Fin (modulus * (modulus * modulus))) :=
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let weights := markedWeights cutoff modulus baselineSign baseline mark
  let result := CurrentFlagDraw.draw weights.data metadata.value.fiber drawBits word
  ⟨result.value, metadata.work + weights.work + result.work + 3⟩

def regularWork (cutoff modulus baselineBits precisionBits drawBits : ℕ) : ℕ :=
  let steps := CurrentFlagTargetNorm.precisionSteps cutoff precisionBits
  CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baselineBits +
    regularWeightWork cutoff modulus baselineBits steps +
    CurrentFlagDraw.workBound (modulus * (modulus * modulus)) (regularWeightHeight cutoff modulus steps) drawBits + 3

def markedWork (cutoff modulus baselineBits drawBits : ℕ) : ℕ :=
  CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baselineBits + markedWeightWork cutoff modulus baselineBits +
    CurrentFlagDraw.workBound (modulus * (modulus * modulus)) (3 * (modulus * (modulus * modulus))) drawBits + 3

theorem regular_work (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ)
    (word : Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2) :
    (regular cutoff modulus baselineSign baseline mark precisionBits drawBits word).work ≤
      regularWork cutoff modulus baseline.length precisionBits drawBits := by
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let steps := CurrentFlagTargetNorm.precisionSteps cutoff precisionBits
  let weights := regularWeights cutoff modulus baselineSign baseline mark steps
  have hm := build_work cutoff modulus false baselineSign [true] baseline mark
  have hw := regularWeights_work cutoff modulus baselineSign baseline mark steps
  have hd := CurrentFlagDraw.draw_work weights.data metadata.value.safe
    (regularWeightHeight cutoff modulus steps) drawBits (regularWeights_height cutoff modulus baselineSign baseline mark steps) word
  change metadata.work ≤ CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baseline.length at hm
  change weights.work ≤ _ at hw
  change metadata.work + weights.work + (CurrentFlagDraw.draw weights.data metadata.value.safe drawBits word).work + 3 ≤ _
  change _ ≤ CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baseline.length +
    regularWeightWork cutoff modulus baseline.length steps +
    CurrentFlagDraw.workBound (modulus * (modulus * modulus)) (regularWeightHeight cutoff modulus steps) drawBits + 3
  omega

theorem marked_work (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (drawBits : ℕ)
    (word : Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2) :
    (marked cutoff modulus baselineSign baseline mark drawBits word).work ≤ markedWork cutoff modulus baseline.length drawBits := by
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let weights := markedWeights cutoff modulus baselineSign baseline mark
  have hm := build_work cutoff modulus false baselineSign [true] baseline mark
  have hw := markedWeights_work cutoff modulus baselineSign baseline mark
  have hd := CurrentFlagDraw.draw_work weights.data metadata.value.fiber
    (3 * (modulus * (modulus * modulus))) drawBits (markedWeights_height cutoff modulus baselineSign baseline mark) word
  change metadata.work ≤ CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baseline.length at hm
  change weights.work ≤ _ at hw
  change metadata.work + weights.work + (CurrentFlagDraw.draw weights.data metadata.value.fiber drawBits word).work + 3 ≤ _
  unfold markedWork
  omega

noncomputable section
open scoped Classical
local instance branchDrawPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance branchDrawNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem inverse_power_half (bits : ℕ) (hbits : 1 ≤ bits) : 1 / (2 : ℝ) ^ bits ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ (2 : ℝ) ^ bits := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbits
  exact one_div_le_one_div_of_le (by norm_num) hp

theorem regular_l1 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((FiniteDist.uniform (Fin (drawBits + Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security) + 1) → Fin 2)).map
      (fun word => (regular (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark precisionBits drawBits word).value)).weight point -
      (CurrentFlagIdealArrays.regularLaw security (signedValue baselineSign baseline) hbaseline mark).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  exact CurrentFlagDraw.draw_l1 _ _ _ (CurrentFlagReferenceSupport.regular_support security baselineSign baseline hbaseline mark)
    (1 / (2 : ℝ) ^ precisionBits) (regularWeights_l1 security baselineSign baseline hbaseline mark precisionBits)
    (inverse_power_half precisionBits hprecision) drawBits

theorem marked_l1 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (drawBits : ℕ) :
    (∑ point, |((FiniteDist.uniform (Fin (drawBits + Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security) + 1) → Fin 2)).map
      (fun word => (marked (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark drawBits word).value)).weight point -
      (CurrentFlagIdealArrays.markedLaw security (signedValue baselineSign baseline) hbaseline mark).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits := by
  have he := CurrentFlagDraw.draw_l1
    (markedWeights (Parameters.sourceCutoff security - 1) (Parameters.modulus security) baselineSign baseline mark).data
    (build (Parameters.sourceCutoff security - 1) (Parameters.modulus security) false baselineSign [true] baseline mark).value.fiber
    (CurrentFlagIdealArrays.markedLaw security (signedValue baselineSign baseline) hbaseline mark)
    (CurrentFlagReferenceSupport.marked_support security baselineSign baseline hbaseline mark) 0
    (by simp only [markedWeights_exact security baselineSign baseline hbaseline mark, sub_self, abs_zero, Finset.sum_const_zero, le_refl])
    (by norm_num) drawBits
  simpa only [marked, mul_zero, add_zero] using he

end
end CurrentAFT.CurrentFlagBranchDraw

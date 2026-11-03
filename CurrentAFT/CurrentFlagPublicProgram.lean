import CurrentAFT.CurrentFlagBinarySemantics
import CurrentAFT.CurrentFlagMetadataSemantics
import CurrentAFT.CurrentFlagTargetNorm

/-!
# Public binary program for the current regular flag branch

Only the public offset, prescribed color, dimensions, and iteration count
are inputs.  No protected first or second source value is observed.  The
generated table has exactly the canonical current response semantics.
-/

namespace CurrentAFT.CurrentFlagPublicProgram

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagFiniteCoordinates CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000

def half : RationalResult := quotient one (ofCounter 2).data

theorem half_value : half.data.decode = (1 / 2 : ℚ) := by
  norm_num [half, quotient_value, one_value, ofCounter_value]

def evaluate (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) (steps : ℕ) :
    ArrayResult (modulus * (modulus * modulus)) :=
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let result := CurrentFlagBinary.regular metadata.value.feature metadata.value.allowed metadata.value.line
    metadata.value.safe metadata.value.fiber half.data steps
  ⟨result.data, metadata.work + half.work + result.work + 3⟩

def workBound (cutoff modulus baselineBits steps : ℕ) : ℕ :=
  CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baselineBits + half.work +
    CurrentFlagBinary.regularWork (modulus * (modulus * modulus)) modulus
      ((2 * cutoff + 1) * (2 * cutoff + 1)) 1 steps + 3

theorem evaluate_work (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) (steps : ℕ) :
    (evaluate cutoff modulus baselineSign baseline mark steps).work ≤ workBound cutoff modulus baseline.length steps := by
  have hm := build_work cutoff modulus false baselineSign [true] baseline mark
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let result := CurrentFlagBinary.regular metadata.value.feature metadata.value.allowed metadata.value.line
    metadata.value.safe metadata.value.fiber half.data steps
  have hh : HeightBound half.data.decode 1 := by rw [half_value]; norm_num [HeightBound]
  have hr := CurrentFlagBinary.regular_work metadata.value.feature metadata.value.allowed metadata.value.line
    metadata.value.safe metadata.value.fiber half.data 1 steps hh
  change result.work ≤ _ at hr
  change metadata.work ≤ CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baseline.length at hm
  change metadata.work + half.work + result.work + 3 ≤ _
  unfold workBound
  omega

theorem evaluate_height (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) (steps : ℕ)
    (point : Fin (modulus * (modulus * modulus))) :
    HeightBound ((evaluate cutoff modulus baselineSign baseline mark steps).data.get point).decode
      (CurrentFlagBinary.iterateHeight (modulus * (modulus * modulus)) modulus
        ((2 * cutoff + 1) * (2 * cutoff + 1)) 1 steps) := by
  have hh : HeightBound half.data.decode 1 := by rw [half_value]; norm_num [HeightBound]
  exact CurrentFlagBinary.regular_height _ _ _ _ _ half.data 1 steps hh point

noncomputable section
open scoped Classical

theorem evaluate_value (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (hsize : 2 * cutoff < modulus) (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus)
    (steps : ℕ) (point : Fin (modulus * (modulus * modulus))) :
    ((evaluate cutoff modulus baselineSign baseline mark steps).data.get point).decode =
      nativeRegular cutoff modulus (signedValue baselineSign baseline) ((ZMod.finEquiv modulus) mark)
        (1 / 2) steps point := by
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  have hf : (fun index point => (metadata.value.feature.get index).get point) = finiteProtectedFeatures cutoff modulus :=
    build_feature cutoff modulus false baselineSign [true] baseline mark
  have ha : (fun index => maskSet (metadata.value.allowed.get index)) =
      finiteProtectedPalettes cutoff modulus 1 (signedValue baselineSign baseline) := by
    funext index
    ext color
    simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (build_allowed cutoff modulus false baselineSign [true] baseline mark index color).trans
      (by rw [CurrentFlagMetadataSemantics.boundary_one])
  have hl : (fun index => metadata.value.line.get index = true) =
      (fun index => (((finiteInputEquiv cutoff index).1 : ℤ) : ZMod modulus) = 0) := by
    funext index
    apply propext
    exact (build_line cutoff modulus false baselineSign [true] baseline mark index).trans
      (first_zero cutoff modulus hsize index).symm
  have hs : (fun input => metadata.value.safe.get input = true) =
      (fun input => input ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
        (finiteProtectedPalettes cutoff modulus 1 (signedValue baselineSign baseline))) := by
    funext input
    apply propext
    exact (build_safe cutoff modulus false baselineSign [true] baseline mark input).trans
      (by rw [CurrentFlagMetadataSemantics.boundary_one])
  have hsp := CurrentFlagMetadataSemantics.fiber_exact cutoff modulus hsize baselineSign baseline mark
  change ((CurrentFlagBinary.regular metadata.value.feature metadata.value.allowed metadata.value.line
    metadata.value.safe metadata.value.fiber half.data steps).data.get point).decode = _
  rw [CurrentFlagBinary.regular_eq_array, CurrentFlagArray.regular_eq, half_value, hf, ha, hl, hs, hsp]
  rfl

local instance publicProgramPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance publicProgramNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem evaluate_current_error (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (bits : ℕ)
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    |(((evaluate (Parameters.sourceCutoff security - 1) (Parameters.modulus security) baselineSign baseline mark
        (CurrentFlagTargetNorm.precisionSteps (Parameters.sourceCutoff security - 1) bits)).data.get point).decode : ℝ) -
      (CurrentFlagProgram.regularDensity
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1
          (signedValue baselineSign baseline)) ((ZMod.finEquiv (Parameters.modulus security)) mark)
        (1 / 2) (finiteChartEquiv (Parameters.modulus security) point) : ℝ)| ≤ 1 / (2 : ℝ) ^ bits := by
  rw [evaluate_value _ _ (AffineFlagCalibration.leg_input_separation security), nativeRegular_eq]
  exact CurrentFlagTargetNorm.current_precision_error security (signedValue baselineSign baseline) hbaseline
    ((ZMod.finEquiv (Parameters.modulus security)) mark) (1 / 2) (by norm_num) (by norm_num) bits point

end
end CurrentAFT.CurrentFlagPublicProgram

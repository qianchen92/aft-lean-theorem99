import CurrentAFT.CurrentFlagIdealArrays

/-! Binary division by the chart count, producing probability-weight arrays. -/

namespace CurrentAFT.CurrentFlagWeightArray

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagPublicProgram CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000

def entry {charts : ℕ} (raw : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
  let value := readVector zero raw point
  let count := ofCounter charts
  let result := quotient value.value count.data
  ⟨result.data, value.work + count.work + result.work + 3⟩

theorem entry_value {charts : ℕ} (raw : Vector RationalBits charts) (point : Fin charts) :
    (entry raw point).data.decode = (raw.get point).decode / charts := by
  simp only [entry, quotient_value, readVector_value, ofCounter_value]

def scale {charts : ℕ} (raw : Vector RationalBits charts) : ArrayResult charts := buildArray charts (entry raw)

theorem scale_value {charts : ℕ} (raw : Vector RationalBits charts) (point : Fin charts) :
    ((scale raw).data.get point).decode = (raw.get point).decode / charts := by
  simp only [scale, buildArray_get, entry_value]

def entryWork (charts height : ℕ) : ℕ :=
  3 * charts + 3 + 60 * (charts + 1) ^ 2 + 2 * primitiveWorkBound (height + charts) + 5

def scaleWork (charts height : ℕ) : ℕ := charts * (entryWork charts height + 2) + 2

theorem entry_height {charts : ℕ} (raw : Vector RationalBits charts) (height : ℕ)
    (hh : ∀ point, HeightBound (raw.get point).decode height) (point : Fin charts) :
    HeightBound (entry raw point).data.decode (height + charts) := by
  rw [entry_value]
  exact (hh point).div (HeightBound.nat_coarse charts)

theorem entry_work {charts : ℕ} (raw : Vector RationalBits charts) (height : ℕ)
    (hh : ∀ point, HeightBound (raw.get point).decode height) (point : Fin charts) :
    (entry raw point).work ≤ entryWork charts height := by
  have hr := readVector_work zero raw point
  have hc := ofCounter_work charts
  have hvalue : HeightBound (readVector zero raw point).value.decode (height + charts) := by
    rw [readVector_value]
    exact (hh point).mono (Nat.le_add_right _ _)
  have hcount : HeightBound (ofCounter charts).data.decode (height + charts) := by
    rw [ofCounter_value]
    exact (HeightBound.nat_coarse charts).mono (Nat.le_add_left _ _)
  have hd := quotient_work (readVector zero raw point).value (ofCounter charts).data (height + charts) hvalue hcount
  simp only [entry, entryWork]
  omega

theorem scale_work {charts : ℕ} (raw : Vector RationalBits charts) (height : ℕ)
    (hh : ∀ point, HeightBound (raw.get point).decode height) :
    (scale raw).work ≤ scaleWork charts height := buildArray_work charts (entryWork charts height) _ (entry_work raw height hh)

def regularWeights (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) (steps : ℕ) :
    ArrayResult (modulus * (modulus * modulus)) :=
  let raw := CurrentFlagPublicProgram.evaluate cutoff modulus baselineSign baseline mark steps
  let weights := scale raw.data
  ⟨weights.data, raw.work + weights.work + 2⟩

def markedWeights (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) :
    ArrayResult (modulus * (modulus * modulus)) :=
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let density := buildArray (modulus * (modulus * modulus)) (chartSpike metadata.value.fiber)
  let weights := scale density.data
  ⟨weights.data, metadata.work + density.work + weights.work + 3⟩

noncomputable section
open scoped Classical
local instance flagWeightPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance flagWeightNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem regularWeights_l1 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (bits : ℕ) :
    (∑ point, |(((regularWeights (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
      baselineSign baseline mark (CurrentFlagTargetNorm.precisionSteps (Parameters.sourceCutoff security - 1) bits)).data.get point).decode : ℝ) -
      (CurrentFlagIdealArrays.regularLaw security (signedValue baselineSign baseline) hbaseline mark).weight point|) ≤
      1 / (2 : ℝ) ^ bits := by
  let N := Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)
  have hN : (0 : ℝ) < N := by dsimp [N]; exact_mod_cast Nat.mul_pos (NeZero.pos _) (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))
  have hp (point : Fin N) :
      |(((regularWeights (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark (CurrentFlagTargetNorm.precisionSteps (Parameters.sourceCutoff security - 1) bits)).data.get point).decode : ℝ) -
        (CurrentFlagIdealArrays.regularLaw security (signedValue baselineSign baseline) hbaseline mark).weight point| ≤
      (1 / (2 : ℝ) ^ bits) / N := by
    have he := CurrentFlagPublicProgram.evaluate_current_error security baselineSign baseline hbaseline mark bits point
    simp only [regularWeights, scale_value, Rat.cast_div, Rat.cast_natCast, CurrentFlagIdealArrays.regular_weight]
    simp only [← Nat.cast_mul]
    rw [← sub_div, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right he hN.le
  have hsum : (∑ _point : Fin N, (1 / (2 : ℝ) ^ bits) / N) = 1 / (2 : ℝ) ^ bits := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hN.ne']
  exact (Finset.sum_le_sum (fun point _ => hp point)).trans_eq hsum

theorem markedWeights_exact (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    (((markedWeights (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
      baselineSign baseline mark).data.get point).decode : ℝ) =
      (CurrentFlagIdealArrays.markedLaw security (signedValue baselineSign baseline) hbaseline mark).weight point := by
  simp only [markedWeights, scale_value, buildArray_get, chartSpike_value, Rat.cast_div, Rat.cast_natCast]
  rw [CurrentFlagMetadataSemantics.fiber_exact _ _ (AffineFlagCalibration.leg_input_separation security),
    CurrentFlagIdealArrays.marked_weight]
  push_cast
  rfl

end
end CurrentAFT.CurrentFlagWeightArray

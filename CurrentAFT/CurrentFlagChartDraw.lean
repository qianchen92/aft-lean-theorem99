import CurrentAFT.CurrentFlagJointDraw

/-! Sampling complete flag and affine charts with binary coordinate decoding. -/

namespace CurrentAFT.CurrentFlagChartDraw

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentFlagJointDraw CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000

def draw (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    CountedValue (Bool × Chart (ZMod modulus)) :=
  let selected := CurrentFlagJointDraw.draw cutoff modulus baselineSign baseline mark precisionBits drawBits word
  let chart := coordinates modulus selected.value.2
  ⟨(selected.value.1, (ZMod.finEquiv modulus) chart.value.1,
      (ZMod.finEquiv modulus) chart.value.2.1, (ZMod.finEquiv modulus) chart.value.2.2),
    selected.work + chart.work + 3⟩

theorem draw_value (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    (draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).value =
      ((Equiv.refl Bool).prodCongr (finiteChartEquiv modulus))
        (CurrentFlagJointDraw.draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).value := by
  let selected := CurrentFlagJointDraw.draw cutoff modulus baselineSign baseline mark precisionBits drawBits word
  have hc := coordinates_field modulus selected.value.2
  change (selected.value.1, (ZMod.finEquiv modulus) (coordinates modulus selected.value.2).value.1,
    (ZMod.finEquiv modulus) (coordinates modulus selected.value.2).value.2.1,
    (ZMod.finEquiv modulus) (coordinates modulus selected.value.2).value.2.2) =
      (selected.value.1, finiteChartEquiv modulus selected.value.2)
  exact congrArg (fun chart => (selected.value.1, chart)) hc

def workBound (cutoff modulus baselineBits precisionBits drawBits : ℕ) : ℕ :=
  CurrentFlagJointDraw.workBound cutoff modulus baselineBits precisionBits drawBits +
    protectedScaleWork modulus (modulus * (modulus * modulus)) + 6

theorem draw_work (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    (draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).work ≤
      workBound cutoff modulus baseline.length precisionBits drawBits := by
  let selected := CurrentFlagJointDraw.draw cutoff modulus baselineSign baseline mark precisionBits drawBits word
  have hs := CurrentFlagJointDraw.draw_work cutoff modulus baselineSign baseline mark precisionBits drawBits word
  have hc := (binaryChartCoordinates_work modulus selected.value.2.val (NeZero.pos _)).trans
    (protectedScaleWork_mono le_rfl selected.value.2.isLt.le)
  change selected.work ≤ _ at hs
  change selected.work + (binaryChartCoordinates modulus selected.value.2.val).work + 3 + 3 ≤ _
  unfold workBound
  omega

noncomputable section
open scoped Classical
local instance chartDrawPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance chartDrawNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem draw_l1 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((tapeLaw (Parameters.modulus security) drawBits).map
      (fun word => (draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark precisionBits drawBits word).value)).weight point -
      (CurrentFlagIdealArrays.model security (signedValue baselineSign baseline) hbaseline mark).model.joint.weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  have hi := joint_l1 security baselineSign baseline hbaseline mark precisionBits drawBits hprecision
  have hm := FiniteDist.l1_map_le
    ((tapeLaw (Parameters.modulus security) drawBits).map (fun word =>
      (CurrentFlagJointDraw.draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark precisionBits drawBits word).value))
    (indexedReference security (signedValue baselineSign baseline) hbaseline mark)
    ((Equiv.refl Bool).prodCongr (finiteChartEquiv (Parameters.modulus security)))
  rw [indexedReference_decode, FiniteDist.map_map] at hm
  simpa only [draw_value, Function.comp_def] using hm.trans hi

theorem completion_l1 (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (baselineSign : Bool) (baseline : List Bool)
    (hencoding : signedValue baselineSign baseline = ActualPublicLegCharge.publicShift security primary seed)
    (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((tapeLaw (Parameters.modulus security) drawBits).map
      (fun word => (draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline primary precisionBits drawBits word).value)).weight point -
      (AffineFlagCalibration.completionLaw security primary seed).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  have hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security := by
    rw [hencoding]
    simpa only [AffineFlagCalibration.legOffsetBound, add_sub_assoc] using
      ActualPublicLegCharge.publicShift_bound security primary seed
  have h := draw_l1 security baselineSign baseline hbaseline primary precisionBits drawBits hprecision
  rw [CurrentFlagCompletion.completionLaw_eq]
  let left : {value : ℤ // |value| ≤ AffineFlagCalibration.legOffsetBound security} :=
    ⟨signedValue baselineSign baseline, hbaseline⟩
  let right : {value : ℤ // |value| ≤ AffineFlagCalibration.legOffsetBound security} :=
    ⟨ActualPublicLegCharge.publicShift security primary seed,
      by simpa only [AffineFlagCalibration.legOffsetBound, add_sub_assoc] using
        ActualPublicLegCharge.publicShift_bound security primary seed⟩
  have heq : left = right := Subtype.ext hencoding
  have hmodel := congrArg (fun value : {value : ℤ // |value| ≤ AffineFlagCalibration.legOffsetBound security} =>
    (CurrentFlagProgram.current security value.val value.property ((ZMod.finEquiv (Parameters.modulus security)) primary)
      (1 / 2 : ℚ) (by norm_num) (by norm_num)).model.joint) heq
  change (CurrentFlagIdealArrays.model security (signedValue baselineSign baseline) hbaseline primary).model.joint =
    (CurrentFlagCompletion.model security primary seed).model.joint at hmodel
  rw [← hmodel]
  exact h

end
end CurrentAFT.CurrentFlagChartDraw

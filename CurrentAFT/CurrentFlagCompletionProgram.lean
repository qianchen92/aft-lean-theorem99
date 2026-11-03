import CurrentAFT.CurrentPublicShiftProgram

/-!
# The executable current completion sampler

The least prime, protected cutoff, and public signed shift are calculated
by checked programs.  Casts identify their verified addresses with the
manuscript types and have no runtime content.
-/

namespace CurrentAFT.CurrentFlagCompletionProgram

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentFlagJointDraw
open scoped BigOperators
set_option maxHeartbeats 500000

def castChart {first second : ℕ} (h : first = second)
    (result : CountedValue (Bool × Chart (ZMod first))) : CountedValue (Bool × Chart (ZMod second)) :=
  ⟨h ▸ result.value, result.work⟩

theorem cast_draw (cutoff first second : ℕ) [NeZero first] [NeZero second] (h : first = second)
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin second) (precisionBits drawBits : ℕ)
    (word : Tape second drawBits) :
    castChart h (CurrentFlagChartDraw.draw cutoff first baselineSign baseline (mark.cast h.symm)
      precisionBits drawBits (cast (congrArg (fun modulus => Tape modulus drawBits) h.symm) word)) =
      CurrentFlagChartDraw.draw cutoff second baselineSign baseline mark precisionBits drawBits word := by
  subst second
  rfl

private instance generatedPrimeNeZero (security : ℕ) : NeZero (PublicParameterProgram.modulus security).count :=
  ⟨by rw [PublicParameterProgram.modulus_value]; exact (Parameters.modulus_spec security).2.ne_zero⟩

def draw (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (precisionBits drawBits : ℕ)
    (word : Tape (Parameters.modulus security) drawBits) :
    CountedValue (Bool × Chart (ZMod (Parameters.modulus security))) :=
  let modulus := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := powerCounter base.count 2
  let cutoff := differenceCounter width.count 1
  let shift := CurrentPublicShiftProgram.current security primary seed
  have hmodulus : modulus.count = Parameters.modulus security := PublicParameterProgram.modulus_value security
  let result := CurrentFlagChartDraw.draw cutoff.count modulus.count shift.value.negative shift.value.digits
    (primary.cast hmodulus.symm) precisionBits drawBits
    (cast (congrArg (fun modulus => Tape modulus drawBits) hmodulus.symm) word)
  let converted := castChart hmodulus result
  ⟨converted.value, modulus.work + base.work + width.work + cutoff.work + shift.work + converted.work + 6⟩

noncomputable section
open scoped Classical
local instance completionProgramPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance completionProgramNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem draw_value (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (precisionBits drawBits : ℕ)
    (word : Tape (Parameters.modulus security) drawBits) :
    (draw security primary seed precisionBits drawBits word).value =
      (CurrentFlagChartDraw.draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        (CurrentPublicShiftProgram.current security primary seed).value.negative
        (CurrentPublicShiftProgram.current security primary seed).value.digits primary precisionBits drawBits word).value := by
  let modulus := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := powerCounter base.count 2
  let cutoff := differenceCounter width.count 1
  let shift := CurrentPublicShiftProgram.current security primary seed
  have hm : modulus.count = Parameters.modulus security := PublicParameterProgram.modulus_value security
  have hc : cutoff.count = Parameters.sourceCutoff security - 1 := by
    simp only [cutoff, width, base, differenceCounter_value, powerCounter_value, addCounter_value,
      Parameters.sourceCutoff, Parameters.base]
  change (castChart hm (CurrentFlagChartDraw.draw cutoff.count modulus.count shift.value.negative shift.value.digits
    (primary.cast hm.symm) precisionBits drawBits
      (cast (congrArg (fun modulus => Tape modulus drawBits) hm.symm) word))).value = _
  rw [cast_draw, hc]

theorem draw_l1 (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((tapeLaw (Parameters.modulus security) drawBits).map
      (fun word => (draw security primary seed precisionBits drawBits word).value)).weight point -
        (AffineFlagCalibration.completionLaw security primary seed).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  have hencoding : signedValue (CurrentPublicShiftProgram.current security primary seed).value.negative
      (CurrentPublicShiftProgram.current security primary seed).value.digits = ActualPublicLegCharge.publicShift security primary seed :=
    CurrentPublicShiftProgram.current_value security primary seed
  simpa only [draw_value] using CurrentFlagChartDraw.completion_l1 security primary seed _ _ hencoding
    precisionBits drawBits hprecision

end
end CurrentAFT.CurrentFlagCompletionProgram

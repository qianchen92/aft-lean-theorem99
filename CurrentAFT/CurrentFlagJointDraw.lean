import CurrentAFT.CurrentFlagBranchDraw
import AFT.FiniteConditionalSampling

/-! The same public fair flag and finite-bit chart law for all protected inputs. -/

namespace CurrentAFT.CurrentFlagJointDraw

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentFlagBranchDraw
open scoped BigOperators
set_option maxHeartbeats 500000

abbrev Tape (modulus drawBits : ℕ) := Bool × (Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2)

def draw (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    CountedValue (Bool × Fin (modulus * (modulus * modulus))) :=
  if word.1 then
    let result := marked cutoff modulus baselineSign baseline mark drawBits word.2
    ⟨(true, result.value), result.work + 2⟩
  else
    let result := regular cutoff modulus baselineSign baseline mark precisionBits drawBits word.2
    ⟨(false, result.value), result.work + 2⟩

theorem draw_value (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    (draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).value =
      (word.1, if word.1 then (marked cutoff modulus baselineSign baseline mark drawBits word.2).value
        else (regular cutoff modulus baselineSign baseline mark precisionBits drawBits word.2).value) := by
  cases h : word.1 <;> simp only [draw, h, Bool.false_eq_true, if_false, if_true]

def workBound (cutoff modulus baselineBits precisionBits drawBits : ℕ) : ℕ :=
  regularWork cutoff modulus baselineBits precisionBits drawBits + markedWork cutoff modulus baselineBits drawBits + 2

theorem draw_work (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    (draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).work ≤
      workBound cutoff modulus baseline.length precisionBits drawBits := by
  have hr := regular_work cutoff modulus baselineSign baseline mark precisionBits drawBits word.2
  have hm := marked_work cutoff modulus baselineSign baseline mark drawBits word.2
  simp only [draw, workBound]
  split <;> dsimp only <;> omega

noncomputable section
open scoped Classical

def tapeLaw (modulus drawBits : ℕ) : FiniteDist (Tape modulus drawBits) :=
  (FiniteDist.uniform Bool).prod (FiniteDist.uniform (Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2))

def branchLaw (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (flag : Bool) :=
  (FiniteDist.uniform (Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2)).map
    (fun word => if flag then (marked cutoff modulus baselineSign baseline mark drawBits word).value
      else (regular cutoff modulus baselineSign baseline mark precisionBits drawBits word).value)

theorem draw_law (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) :
    (tapeLaw modulus drawBits).map (fun word => (draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).value) =
      FiniteDist.joint (FiniteDist.uniform Bool) (branchLaw cutoff modulus baselineSign baseline mark precisionBits drawBits) := by
  simp only [draw_value, tapeLaw]
  have h := FiniteDist.map_joint_program (FiniteDist.uniform Bool)
    (FiniteDist.uniform (Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2)) id
    (fun flag word => if flag then (marked cutoff modulus baselineSign baseline mark drawBits word).value
      else (regular cutoff modulus baselineSign baseline mark precisionBits drawBits word).value)
  have hid : (FiniteDist.uniform Bool).map id = FiniteDist.uniform Bool := by
    ext flag
    simp
  simpa only [hid, id_eq, branchLaw] using h

local instance jointDrawPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance jointDrawNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

def referenceBranches (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (flag : Bool) :=
  if flag then CurrentFlagIdealArrays.markedLaw security baseline hbaseline mark
    else CurrentFlagIdealArrays.regularLaw security baseline hbaseline mark

def indexedReference (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) :=
  FiniteDist.joint (FiniteDist.uniform Bool) (referenceBranches security baseline hbaseline mark)

theorem joint_l1 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((tapeLaw (Parameters.modulus security) drawBits).map
      (fun word => (draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark precisionBits drawBits word).value)).weight point -
      (indexedReference security (signedValue baselineSign baseline) hbaseline mark).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  rw [draw_law]
  have h := FiniteDist.l1_joint_uniform (FiniteDist.uniform Bool) (FiniteDist.uniform Bool)
    (branchLaw (Parameters.sourceCutoff security - 1) (Parameters.modulus security) baselineSign baseline mark precisionBits drawBits)
    (referenceBranches security (signedValue baselineSign baseline) hbaseline mark)
    (1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits)) (fun flag => ?_)
  · simpa only [indexedReference, sub_self, abs_zero, Finset.sum_const_zero, zero_add] using h
  · cases flag
    · simpa only [branchLaw, referenceBranches, Bool.false_eq_true, if_false] using
        regular_l1 security baselineSign baseline hbaseline mark precisionBits drawBits hprecision
    · apply le_trans _ (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 4 * (1 / (2 : ℝ) ^ precisionBits)))
      simpa only [branchLaw, referenceBranches, if_true] using marked_l1 security baselineSign baseline hbaseline mark drawBits

theorem indexedReference_decode (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ AffineFlagCalibration.legOffsetBound security) (mark : Fin (Parameters.modulus security)) :
    (indexedReference security baseline hbaseline mark).map
      ((Equiv.refl Bool).prodCongr (finiteChartEquiv (Parameters.modulus security))) =
      (CurrentFlagIdealArrays.model security baseline hbaseline mark).model.joint := by
  ext point
  rw [FiniteDist.map_equiv_weight]
  rw [(CurrentFlagIdealArrays.model security baseline hbaseline mark).model.decomposition]
  cases flagEq : point.1 <;>
    simp [indexedReference, referenceBranches, FiniteDist.joint, CurrentFlagIdealArrays.regularLaw,
      CurrentFlagIdealArrays.markedLaw, FiniteDist.map_equiv_weight, FiniteDist.uniform_weight,
      Equiv.prodCongr_symm, flagEq]
  norm_num

end
end CurrentAFT.CurrentFlagJointDraw

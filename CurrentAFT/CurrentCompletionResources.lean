import CurrentAFT.CurrentPublicCompletion
import CurrentAFT.CurrentProposalSamplerPolynomial
import CurrentAFT.UniformPolynomialBound
import CurrentAFT.CurrentFlagCostPolynomial
import AFT.BinaryProtectedPolynomialBound

/-! Polynomial work of the actual completed public flag/chart draws.
All public inputs are stored by the proposal; no chart or shift oracle is
supplied to the runtime theorem. -/
namespace CurrentAFT.CurrentCompletionResources
open AFT BinaryArithmetic RationalNumerics RationalRejectionProgram
open BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount
  CurrentFlagCompletionProgram.draw CurrentChartsDraw.draw PublicParameterProgram.modulus

theorem chart_baseline_mono (cutoff modulus first second precision bits : ℕ) (h : first ≤ second) :
    CurrentFlagChartDraw.workBound cutoff modulus first precision bits ≤
      CurrentFlagChartDraw.workBound cutoff modulus second precision bits := by
  have hm := protectedMetadataWork_mono (Nat.le_refl cutoff) (Nat.le_refl modulus) (Nat.le_refl 1) h
  simp only [CurrentFlagChartDraw.workBound, CurrentFlagJointDraw.workBound,
    CurrentFlagBranchDraw.regularWork, CurrentFlagBranchDraw.markedWork,
    CurrentFlagWeightArray.regularWeightWork, CurrentFlagWeightArray.markedWeightWork,
    CurrentFlagPublicProgram.workBound, CurrentFlagBinaryMetadata.workBound]
  omega

def flagWork (security precision bits : ℕ) : ℕ :=
  PublicParameterProgram.workBound security+(2*security+1)+powerCounterWork (security+2) 2+
    (2*(security+2)^2+1)+CurrentPublicShiftProgram.workBound security+
    CurrentFlagChartDraw.workBound (Parameters.sourceCutoff security-1) (Parameters.modulus security)
      (2*(security+2)^48+2*(security+2)^2+2) precision bits+6

theorem flag_work (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (precision bits : ℕ)
    (word : CurrentFlagJointDraw.Tape (Parameters.modulus security) bits) :
    (CurrentFlagCompletionProgram.draw security primary seed precision bits word).work ≤ flagWork security precision bits := by
  have hm := PublicParameterProgram.modulus_work security
  have hb := addCounter_work security 2
  have hp := powerCounter_work (security+2) 2
  have hc := differenceCounter_work ((security+2)^2) 1
  have hs := CurrentPublicShiftProgram.current_work security primary seed
  have hl := CurrentPublicShiftProgram.current_length security primary seed
  have hd := (CurrentFlagChartDraw.draw_work (Parameters.sourceCutoff security-1) (Parameters.modulus security)
    (CurrentPublicShiftProgram.current security primary seed).value.negative
    (CurrentPublicShiftProgram.current security primary seed).value.digits primary precision bits word).trans
      (chart_baseline_mono _ _ _ _ _ _ hl)
  have hv : (differenceCounter (powerCounter (addCounter security 2).count 2).count 1).count = Parameters.sourceCutoff security-1 := by
    simp only [differenceCounter_value, powerCounter_value, addCounter_value, Parameters.sourceCutoff, Parameters.base]
  unfold CurrentFlagCompletionProgram.draw
  change (PublicParameterProgram.modulus security).work+(addCounter security 2).work+
    (powerCounter (addCounter security 2).count 2).work+
    (differenceCounter (powerCounter (addCounter security 2).count 2).count 1).work+
    (CurrentPublicShiftProgram.current security primary seed).work+
    (CurrentFlagCompletionProgram.castChart (PublicParameterProgram.modulus_value security)
      (CurrentFlagChartDraw.draw (differenceCounter (powerCounter (addCounter security 2).count 2).count 1).count
        (PublicParameterProgram.modulus security).count
        (CurrentPublicShiftProgram.current security primary seed).value.negative
        (CurrentPublicShiftProgram.current security primary seed).value.digits
        (primary.cast (PublicParameterProgram.modulus_value security).symm) precision bits
        (cast (congrArg (fun modulus => CurrentFlagJointDraw.Tape modulus bits)
          (PublicParameterProgram.modulus_value security).symm) word))).work+6 ≤ _
  rw [CurrentFlagCompletionProgram.cast_draw, hv, addCounter_value, powerCounter_value]
  unfold flagWork
  omega

def chartsWork (security precision bits : ℕ) : ℕ :=
  (2*security+1)+powerCounterWork (security+2) 128+
    Parameters.legCount security*(3*Parameters.legCount security+flagWork security precision bits+7)+5

theorem charts_work (security : ℕ) (inputs : CurrentChartsDraw.InputVector security) (precision bits : ℕ)
    (word : CurrentChartsDraw.Tapes security bits) :
    (CurrentChartsDraw.draw security inputs precision bits word).work ≤ chartsWork security precision bits := by
  let count := powerCounter (addCounter security 2).count 128
  have hc : count.count = Parameters.legCount security := by
    simp only [count, powerCounter_value, addCounter_value, Parameters.legCount_eq, Parameters.base]
  let term (index : Fin count.count) : CountedValue (Bool × BoundaryCalibration.Chart (ZMod (Parameters.modulus security))) :=
    let leg := index.cast hc
    let input := readVector (CurrentChartsDraw.defaultInput security) inputs leg
    let result := CurrentFlagCompletionProgram.draw security input.value.1 input.value.2 precision bits (word leg)
    ⟨result.value, input.work+result.work+2⟩
  have ht (index : Fin count.count) : (term index).work ≤ 3*Parameters.legCount security+flagWork security precision bits+5 := by
    have hr := readVector_work (CurrentChartsDraw.defaultInput security) inputs (index.cast hc)
    have hd := flag_work security (readVector (CurrentChartsDraw.defaultInput security) inputs (index.cast hc)).value.1
      (readVector (CurrentChartsDraw.defaultInput security) inputs (index.cast hc)).value.2 precision bits (word (index.cast hc))
    dsimp only [term]
    omega
  have hs := storeData_work count.count (3*Parameters.legCount security+flagWork security precision bits+5) term ht
  have hp := powerCounter_work (security+2) 128
  have hb := addCounter_work security 2
  unfold CurrentChartsDraw.draw CurrentChartsDraw.drawStored
  change (addCounter security 2).work+count.work+(storeData count.count term).work+3 ≤ _
  conv_rhs at hs => rw [hc]
  simp only [Nat.add_assoc, show (5 : ℕ)+2=7 by decide] at hs
  have hcp : count.work ≤ powerCounterWork (security+2) 128 := by simpa only [count, addCounter_value] using hp
  unfold chartsWork
  simp only [Nat.add_assoc] at hs ⊢
  omega

def work (security precision bits edgeBits : ℕ) : ℕ :=
  chartsWork security precision bits+CurrentEdgeDrawProgram.workBound security edgeBits+3

theorem complete_work (security precision bits edgeBits : ℕ) (input : Option (CurrentPublicCompletion.CachedCore security))
    (word : CurrentPublicCompletion.Tapes security bits edgeBits) :
    (CurrentPublicCompletion.complete security input precision bits edgeBits word).work ≤ work security precision bits edgeBits := by
  cases input with
  | none => change 1 ≤ _; unfold work; omega
  | some cached =>
    have hc := charts_work security cached.inputs precision bits word.1
    have he := CurrentEdgeDrawProgram.draw_work security edgeBits word.2
    change (CurrentChartsDraw.draw security cached.inputs precision bits word.1).work+
      (CurrentEdgeDrawProgram.draw security edgeBits word.2).work+3 ≤ _
    unfold work
    omega

noncomputable section
open Polynomial

def flagPolynomial (precision bits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+(2*X+1)+3*(6*(X+3)^4+4)+(2*(X+2)^2+1)+
    CurrentProposalResources.shiftWorkPolynomial+
    CurrentFlagCostPolynomial.current ((X+2)^2) CurrentProposalResources.primeSizePolynomial
      (2*(X+2)^48+2*(X+2)^2+2) precision bits+6

theorem flag_polynomial (security : ℕ) (precision bits : Polynomial ℕ) :
    flagWork security (precision.eval security) (bits.eval security) ≤ (flagPolynomial precision bits).eval security := by
  have hc : Parameters.sourceCutoff security-1 ≤ (security+2)^2 := by
    simpa only [Parameters.sourceCutoff, Parameters.base] using Nat.sub_le (Parameters.sourceCutoff security) 1
  have hq : Parameters.modulus security ≤ CurrentProposalResources.primeSizePolynomial.eval security := by
    simpa only [CurrentProposalResources.primeSizePolynomial, eval_mul, eval_pow, eval_add, eval_X, eval_ofNat,
      Parameters.base] using (Parameters.modulus_bounds security).2
  have hd := CurrentFlagCostPolynomial.work_mono hc hq
    (Nat.le_refl (2*(security+2)^48+2*(security+2)^2+2))
    (Nat.le_refl (precision.eval security)) (Nat.le_refl (bits.eval security))
  simp only [flagPolynomial, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X, eval_one,
    PublicParameterProgram.workPolynomial_eval, CurrentProposalResources.shiftWorkPolynomial_eval,
    CurrentFlagCostPolynomial.current_eval]
  unfold flagWork powerCounterWork
  norm_num only
  rw [show security+2+1 = security+3 by omega]
  omega

def chartsPolynomial (precision bits : Polynomial ℕ) : Polynomial ℕ :=
  let count := CurrentProposalResources.countPolynomial
  (2*X+1)+129*(6*(X+3)^130+4)+count*(3*count+flagPolynomial precision bits+7)+5

theorem charts_polynomial (security : ℕ) (precision bits : Polynomial ℕ) :
    chartsWork security (precision.eval security) (bits.eval security) ≤ (chartsPolynomial precision bits).eval security := by
  have hs := (CurrentProposalResources.count_bounds security).2.1
  rw [(CurrentProposalDimensions.current_values security).2.1] at hs
  have hf := flag_polynomial security precision bits
  have hm := Nat.mul_le_mul hs (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 3 hs) hf) 7)
  simp only [chartsPolynomial, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X, eval_one]
  unfold chartsWork powerCounterWork
  norm_num only
  rw [show security+2+1 = security+3 by omega]
  omega

def workPolynomial (precision bits edgeBits : Polynomial ℕ) : Polynomial ℕ :=
  chartsPolynomial precision bits+CurrentProposalSamplerPolynomial.edgeWorkPolynomial edgeBits+3

theorem complete_polynomial_work (security : ℕ) (precision bits edgeBits : Polynomial ℕ)
    (input : Option (CurrentPublicCompletion.CachedCore security))
    (word : CurrentPublicCompletion.Tapes security (bits.eval security) (edgeBits.eval security)) :
    (CurrentPublicCompletion.complete security input (precision.eval security) (bits.eval security) (edgeBits.eval security) word).work ≤
      (workPolynomial precision bits edgeBits).eval security := by
  have hc := charts_polynomial security precision bits
  have he := CurrentProposalSamplerPolynomial.edge_work security edgeBits
  have h := complete_work security (precision.eval security) (bits.eval security) (edgeBits.eval security) input word
  unfold work at h
  simp only [workPolynomial, eval_add, eval_ofNat]
  omega

end
end CurrentAFT.CurrentCompletionResources

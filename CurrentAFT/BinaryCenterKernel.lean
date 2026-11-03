import CurrentAFT.BinaryCenterFormula
import CurrentAFT.BinaryWindowAverage
import AFT.BinaryMatrixArray
import AFT.BinarySliceProbability

/-! # Center entries from already generated binary reference arrays -/
namespace CurrentAFT.BinaryCenterKernel
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter

def anchorEntry {count : ℕ} (anchor : Vector (Vector RationalBits count) count)
    (output input : Fin count) : RationalResult :=
  let result := matrixEntry anchor input output
  ⟨result.value, result.work+1⟩

theorem anchorEntry_value {count : ℕ} (anchor : Vector (Vector RationalBits count) count)
    (output input : Fin count) :
    (anchorEntry anchor output input).data.decode = ((anchor.get input).get output).decode := by
  simp only [anchorEntry, matrixEntry_value]

def anchorAverage {count : ℕ} (primary : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (output : Fin count) : RationalResult :=
  BinaryWindowAverage.sum primary (anchorEntry anchor output)

theorem anchorAverage_value {count : ℕ} (primary : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (output : Fin count) :
    (anchorAverage primary anchor output).data.decode =
      ∑ input, (primary.get input).decode*((anchor.get input).get output).decode := by
  simp only [anchorAverage, BinaryWindowAverage.sum_value, anchorEntry_value]

theorem anchorAverage_bounds {count : ℕ} (primary : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (output : Fin count) (height : ℕ)
    (hp : ∀ input, HeightBound (primary.get input).decode height)
    (ha : ∀ input output, HeightBound ((anchor.get input).get output).decode height) :
    HeightBound (anchorAverage primary anchor output).data.decode (count*(2*height+1)) ∧
      (anchorAverage primary anchor output).work ≤ BinaryWindowAverage.sumWork count height height (7*count+9) := by
  have hh (input : Fin count) : HeightBound (anchorEntry anchor output input).data.decode height := by
    rw [anchorEntry_value]; exact ha input output
  have hw (input : Fin count) : (anchorEntry anchor output input).work ≤ 7*count+9 := by
    have hm := matrixEntry_work anchor input output
    change (matrixEntry anchor input output).work+1 ≤ _
    omega
  simpa only [anchorAverage, BinaryWindowAverage.sumHeight, two_mul] using
    BinaryWindowAverage.sum_bounds primary (anchorEntry anchor output) height height (7*count+9) hp hh hw

def safe (count margin : ℕ) (output : Fin count) : RationalResult :=
  let colors := canonicalCounter count
  let boundary := canonicalCounter margin
  let color := canonicalCounter output.val
  let result := binarySliceProbability false false false false colors.digits boundary.digits [] color.digits
  ⟨result.data, colors.work+boundary.work+color.work+result.work+4⟩

theorem safe_value (count margin : ℕ) (output : Fin count) :
    (safe count margin output).data.decode = AFT.V7Calibration.sliceProbabilityProgram count margin 0 output.val := by
  simp only [safe, binarySliceProbability_value, signedValue, canonicalCounter_value, value, Bool.false_eq_true, if_false, Nat.cast_zero]

def integerBound (count margin : ℕ) : ℕ := count+margin+1

theorem safe_bounds (count margin : ℕ) (output : Fin count) :
    HeightBound (safe count margin output).data.decode (integerBound count margin+3) ∧
      (safe count margin output).work ≤ 3*(50*(integerBound count margin+1)^2)+
        binarySliceProbabilityWork (integerBound count margin)+4 := by
  let bound := integerBound count margin
  have hc : count ≤ bound := by unfold bound integerBound; omega
  have hm : margin ≤ bound := by unfold bound integerBound; omega
  have ho : output.val ≤ bound := (Nat.le_of_lt output.isLt).trans hc
  have len (number : ℕ) (hn : number ≤ bound) : (canonicalCounter number).digits.length ≤ bound := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := number))).trans hn
  have work (number : ℕ) (hn : number ≤ bound) : (canonicalCounter number).work ≤ 50*(bound+1)^2 :=
    (canonicalCounter_work number).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2))
  have hs := binarySliceProbability_height false false false false (canonicalCounter count).digits
    (canonicalCounter margin).digits [] (canonicalCounter output.val).digits bound (len count hc) (len margin hm) (by simp)
  have ws := binarySliceProbability_work false false false false (canonicalCounter count).digits
    (canonicalCounter margin).digits [] (canonicalCounter output.val).digits bound (len count hc) (len margin hm) (by simp) (len output.val ho)
  have wc := work count hc
  have wm := work margin hm
  have wo := work output.val ho
  dsimp only [bound] at ws wc wm wo
  exact ⟨hs, by change _+_+_+_+4 ≤ _; omega⟩

def point {count : ℕ} (margin : ℕ) (metadata : BinaryProposalMetadata.Encoded) (rate : RationalBits)
    (primary : Vector RationalBits count) (anchor : Vector (Vector RationalBits count) count)
    (output : Fin count) : RationalResult :=
  let first := safe count margin output
  let average := anchorAverage primary anchor output
  let result := BinaryCenterFormula.current metadata rate first.data average.data
  ⟨result.data, first.work+average.work+result.work+3⟩

theorem point_value {count : ℕ} (margin : ℕ) (metadata : BinaryProposalMetadata.Encoded) (rate : RationalBits)
    (primary : Vector RationalBits count) (anchor : Vector (Vector RationalBits count) count) (output : Fin count) :
    (point margin metadata rate primary anchor output).data.decode =
      (1+metadata.legs.decode*rate.decode/(metadata.population.decode-metadata.legs.decode-metadata.colors.decode))*
        AFT.V7Calibration.sliceProbabilityProgram count margin 0 output.val-
      metadata.legs.decode*rate.decode/(metadata.population.decode-metadata.legs.decode-metadata.colors.decode)*
        ∑ input, (primary.get input).decode*((anchor.get input).get output).decode := by
  simp only [point, BinaryCenterFormula.current_value, safe_value, anchorAverage_value]

def formulaBound (count margin height : ℕ) : ℕ := height+(integerBound count margin+3)+count*(2*height+1)
def height (count margin bound : ℕ) : ℕ := BinaryCenterFormula.height (formulaBound count margin bound)
def work (count margin bound : ℕ) : ℕ :=
  3*(50*(integerBound count margin+1)^2)+binarySliceProbabilityWork (integerBound count margin)+4+
    BinaryWindowAverage.sumWork count bound bound (7*count+9)+BinaryCenterFormula.work (formulaBound count margin bound)+3

theorem point_bounds {count : ℕ} (margin : ℕ) (metadata : BinaryProposalMetadata.Encoded) (rate : RationalBits)
    (primary : Vector RationalBits count) (anchor : Vector (Vector RationalBits count) count) (output : Fin count)
    (bound : ℕ) (hq : HeightBound metadata.colors.decode bound) (hl : HeightBound metadata.legs.decode bound)
    (hd : HeightBound metadata.population.decode bound) (hr : HeightBound rate.decode bound)
    (hp : ∀ input, HeightBound (primary.get input).decode bound)
    (ha : ∀ input output, HeightBound ((anchor.get input).get output).decode bound) :
    HeightBound (point margin metadata rate primary anchor output).data.decode (height count margin bound) ∧
      (point margin metadata rate primary anchor output).work ≤ work count margin bound := by
  let B := formulaBound count margin bound
  have hb : bound ≤ B := by unfold B formulaBound; omega
  have hs := safe_bounds count margin output
  have hav := anchorAverage_bounds primary anchor output bound hp ha
  have hf := BinaryCenterFormula.current_bounds metadata rate (safe count margin output).data
    (anchorAverage primary anchor output).data B (hq.mono hb) (hl.mono hb) (hd.mono hb) (hr.mono hb)
    (hs.1.mono (by unfold B formulaBound; omega)) (hav.1.mono (by unfold B formulaBound; omega))
  dsimp only [B] at hf
  exact ⟨hf.1, by
    change (safe count margin output).work+(anchorAverage primary anchor output).work+
      (BinaryCenterFormula.current metadata rate (safe count margin output).data (anchorAverage primary anchor output).data).work+3 ≤ _
    unfold work
    omega⟩

noncomputable def formulaPolynomial (count margin bound : Polynomial ℕ) : Polynomial ℕ :=
  bound+(count+margin+1+3)+count*(2*bound+1)
noncomputable def heightPolynomial (count margin bound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCenterFormula.heightPolynomial (formulaPolynomial count margin bound)
noncomputable def sliceWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  100*(bits+2)+20*(bits+2)+11+200*(bits+5)+primitiveWorkPolynomial (bits+3)

noncomputable def workPolynomial (count margin bound : Polynomial ℕ) : Polynomial ℕ :=
  3*(50*(count+margin+1+1)^2)+sliceWorkPolynomial (count+margin+1)+4+
    BinaryWindowAverage.sumWorkPolynomial count bound bound (7*count+9)+
    BinaryCenterFormula.workPolynomial (formulaPolynomial count margin bound)+3

theorem formulaPolynomial_eval (count margin bound : Polynomial ℕ) (security : ℕ) :
    (formulaPolynomial count margin bound).eval security = formulaBound (count.eval security) (margin.eval security) (bound.eval security) := by
  simp only [formulaPolynomial, formulaBound, integerBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]

theorem heightPolynomial_eval (count margin bound : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial count margin bound).eval security = height (count.eval security) (margin.eval security) (bound.eval security) := by
  rw [heightPolynomial, BinaryCenterFormula.heightPolynomial_eval, formulaPolynomial_eval]
  rfl

theorem workPolynomial_eval (count margin bound : Polynomial ℕ) (security : ℕ) :
    (workPolynomial count margin bound).eval security = work (count.eval security) (margin.eval security) (bound.eval security) := by
  simp only [workPolynomial, work, BinaryCenterFormula.workPolynomial_eval, formulaPolynomial_eval,
    BinaryWindowAverage.sumWorkPolynomial, BinaryWindowAverage.termWorkPolynomial, BinaryWindowAverage.sumWork,
    BinaryWindowAverage.termWork, sliceWorkPolynomial, binarySliceProbabilityWork, binaryEndpointProbabilityWork, binaryIntervalProbabilityWork,
    primitiveWorkPolynomial_eval, integerBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  simp only [Nat.add_assoc, Nat.reduceAdd]

end CurrentAFT.BinaryCenterKernel

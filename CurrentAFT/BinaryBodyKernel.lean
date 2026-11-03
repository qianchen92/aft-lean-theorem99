import CurrentAFT.BinaryAnchorProgram
import AFT.BinaryIntegerDivision

/-! # The translated safe-body kernel with genuine binary residues

The finite palette sum retains the exact modular shift. Every baseline,
residue, comparison and safe-interval probability is computed explicitly.
-/
namespace CurrentAFT.BinaryBodyKernel
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter signedAdd IntegerBits.residue

def atBaseline {colors : ℕ} (modulus margin : List Bool) (shiftSign : Bool) (shift output : List Bool)
    (baseline : Fin colors) : RationalResult :=
  let color := canonicalCounter baseline.val
  let translated := signedAdd false shiftSign color.digits shift
  let residue := IntegerBits.residue ⟨translated.negative, translated.digits⟩ modulus
  let matched := signedEqual false false residue.digits output
  let probability := binarySliceProbability false false false false modulus margin [] color.digits
  ⟨if matched.value then probability.data else zero,
    color.work + translated.work + residue.work + matched.work + probability.work + 5⟩

theorem atBaseline_value {colors : ℕ} (modulus margin : List Bool) (shiftSign : Bool) (shift output : List Bool)
    (baseline : Fin colors) (hq : 0 < value modulus) :
    (atBaseline modulus margin shiftSign shift output baseline).data.decode =
      if ((baseline.val:ℤ)+signedValue shiftSign shift)%(value modulus:ℤ) = (value output:ℤ)
      then RationalProposalProgram.safeEntry (value modulus) (value margin) baseline.val else 0 := by
  have hres := IntegerBits.residue_value
    (⟨(signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).negative,
      (signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).digits⟩ : IntegerBits) modulus hq
  have hv : (⟨(signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).negative,
      (signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).digits⟩ : IntegerBits).decode =
      (baseline.val:ℤ)+signedValue shiftSign shift := by
    rw [IntegerBits.decode, signedAdd_value]
    simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value]
  have hm : (signedEqual false false
      (IntegerBits.residue ⟨(signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).negative,
        (signedAdd false shiftSign (canonicalCounter baseline.val).digits shift).digits⟩ modulus).digits output).value = true ↔
      ((baseline.val:ℤ)+signedValue shiftSign shift)%(value modulus:ℤ) = (value output:ℤ) := by
    rw [signedEqual_value]
    simp only [signedValue, Bool.false_eq_true, if_false]
    rw [hres, hv]
    rfl
  unfold atBaseline
  dsimp only
  simp only [hm]
  split_ifs
  · rw [binarySliceProbability_value]
    simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value]
    norm_num [value]
    rfl
  · exact zero_value

def baselineHeight (bound : ℕ) : ℕ := bound+3
def baselineWork (bound : ℕ) : ℕ :=
  50*(bound+1)^2 + (20*bound+8) + (60*(2*bound+2)^2+10) +
    (48*(2*bound+1)+39) + binarySliceProbabilityWork bound + 5

theorem atBaseline_bounds {colors : ℕ} (modulus margin : List Bool) (shiftSign : Bool) (shift output : List Bool)
    (baseline : Fin colors) (bound : ℕ) (hc : colors ≤ bound) (hq : modulus.length ≤ bound)
    (hm : margin.length ≤ bound) (hs : shift.length ≤ bound) (ho : output.length ≤ bound) :
    HeightBound (atBaseline modulus margin shiftSign shift output baseline).data.decode (baselineHeight bound) ∧
      (atBaseline modulus margin shiftSign shift output baseline).work ≤ baselineWork bound := by
  let color := canonicalCounter baseline.val
  let translated := signedAdd false shiftSign color.digits shift
  let residue := IntegerBits.residue ⟨translated.negative, translated.digits⟩ modulus
  have hi : baseline.val ≤ bound := baseline.isLt.le.trans hc
  have hcolor : color.digits.length ≤ bound := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := baseline.val))).trans hi
  have htranslated : translated.digits.length ≤ bound+1 := (signedAdd_length _ _ _ _).trans (by omega)
  have hres : residue.digits.length ≤ 2*bound+1 := (IntegerBits.residue_length _ _).trans (by dsimp only; omega)
  have hprob := binarySliceProbability_height false false false false modulus margin [] color.digits bound hq hm (by simp)
  have wc : color.work ≤ 50*(bound+1)^2 := (canonicalCounter_work baseline.val).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have wt : translated.work ≤ 20*bound+8 := (signedAdd_work _ _ _ _).trans (by omega)
  have wr : residue.work ≤ 60*(2*bound+2)^2+10 :=
    (IntegerBits.residue_work (⟨translated.negative, translated.digits⟩ : IntegerBits) modulus).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left
        (show translated.digits.length+modulus.length+1 ≤ 2*bound+2 by omega) 2)) 10)
  have wm := signedEqual_work false false residue.digits output
  have wp := binarySliceProbability_work false false false false modulus margin [] color.digits bound hq hm (by simp) hcolor
  constructor
  · unfold atBaseline
    dsimp only
    split
    · exact hprob
    · exact HeightBound.zero.mono (by omega)
  · change color.work + translated.work + residue.work + (signedEqual false false residue.digits output).work +
      (binarySliceProbability false false false false modulus margin [] color.digits).work + 5 ≤ _
    unfold baselineWork
    omega

def translated (colors margin : ℕ) (shiftSign : Bool) (shift output : List Bool) : RationalResult :=
  let modulusCode := canonicalCounter colors
  let marginCode := canonicalCounter margin
  let result := sumFin colors (atBaseline modulusCode.digits marginCode.digits shiftSign shift output)
  ⟨result.data, modulusCode.work + marginCode.work + result.work + 3⟩

theorem translated_value (colors margin : ℕ) (shiftSign : Bool) (shift output : List Bool) (hq : 0 < colors) :
    (translated colors margin shiftSign shift output).data.decode =
      RationalProposalProgram.bodyKernel colors margin (signedValue shiftSign shift) (value output) := by
  simp only [translated, sumFin_value]
  have hcode : 0 < value (canonicalCounter colors).digits := by rw [canonicalCounter_value]; exact hq
  simp_rw [atBaseline_value (canonicalCounter colors).digits (canonicalCounter margin).digits shiftSign shift output _ hcode]
  simp only [canonicalCounter_value]
  rfl

def translatedWork (bound : ℕ) : ℕ := 100*(bound+1)^2 +
  bound*(baselineWork bound+primitiveWorkBound ((bound+1)*(bound+4))+2)+5

theorem translated_bounds (colors margin : ℕ) (shiftSign : Bool) (shift output : List Bool) (bound : ℕ)
    (hc : colors ≤ bound) (hm : margin ≤ bound) (hs : shift.length ≤ bound) (ho : output.length ≤ bound) :
    HeightBound (translated colors margin shiftSign shift output).data.decode (bound*(bound+4)) ∧
      (translated colors margin shiftSign shift output).work ≤ translatedWork bound := by
  let modulusCode := canonicalCounter colors
  let marginCode := canonicalCounter margin
  have hmod : modulusCode.digits.length ≤ bound := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := colors))).trans hc
  have hmargin : marginCode.digits.length ≤ bound := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := margin))).trans hm
  have ht (baseline : Fin colors) := atBaseline_bounds modulusCode.digits marginCode.digits shiftSign shift output baseline
    bound hc hmod hmargin hs ho
  have hh := sumFin_height colors (baselineHeight bound) _ (fun baseline => (ht baseline).1)
  have ww := sumFin_work colors (baselineHeight bound) (baselineWork bound) _
    (fun baseline => (ht baseline).1) (fun baseline => (ht baseline).2)
  have wq : modulusCode.work ≤ 50*(bound+1)^2 := (canonicalCounter_work colors).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have wm : marginCode.work ≤ 50*(bound+1)^2 := (canonicalCounter_work margin).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  constructor
  · exact hh.mono (by unfold baselineHeight; gcongr)
  · have wsum : (sumFin colors (atBaseline modulusCode.digits marginCode.digits shiftSign shift output)).work ≤
        bound*(baselineWork bound+primitiveWorkBound ((bound+1)*(bound+4))+2)+2 := by
      apply ww.trans
      unfold baselineHeight primitiveWorkBound
      gcongr
    change modulusCode.work + marginCode.work +
      (sumFin colors (atBaseline modulusCode.digits marginCode.digits shiftSign shift output)).work + 3 ≤ _
    unfold translatedWork
    omega

noncomputable def sliceWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  100*(bound+2)+20*(bound+2)+11+200*(bound+5)+primitiveWorkPolynomial (bound+3)
noncomputable def baselineWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  50*(bound+1)^2+(20*bound+8)+(60*(2*bound+2)^2+10)+(48*(2*bound+1)+39)+sliceWorkPolynomial bound+5
noncomputable def translatedWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  100*(bound+1)^2+bound*(baselineWorkPolynomial bound+primitiveWorkPolynomial ((bound+1)*(bound+4))+2)+5

theorem translatedWorkPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (translatedWorkPolynomial bound).eval security = translatedWork (bound.eval security) := by
  simp only [translatedWorkPolynomial, baselineWorkPolynomial, sliceWorkPolynomial,
    translatedWork, baselineWork, binarySliceProbabilityWork, binaryEndpointProbabilityWork,
    binaryIntervalProbabilityWork, primitiveWorkPolynomial_eval, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring_nf

end CurrentAFT.BinaryBodyKernel

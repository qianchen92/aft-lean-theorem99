import CurrentAFT.BinaryRootMeanResources

/-! # The actual singleton mass lifts have polynomial bit height and work -/
namespace CurrentAFT.BinaryRootProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current BinaryPaletteLookup.current
  BinaryShiftedSafeProfile.current PublicParameterProgram.modulus BinaryActivationProgram.cutoff
  BinaryRootConvolution.current BinaryMassLiftInput.current
noncomputable section

def deviationOperandPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  shiftedHeightPolynomial precision queueBits rootBits inputBits+meanHeightPolynomial precision queueBits inputBits
def deviationHeightPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  deviationOperandPolynomial precision queueBits rootBits inputBits+1
def deviationWorkPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  shiftedWorkPolynomial precision queueBits rootBits inputBits+meanWorkPolynomial precision queueBits inputBits+
    2*primitiveWorkPolynomial (deviationOperandPolynomial precision queueBits rootBits inputBits)+5

theorem deviation_bounds (security : ℕ) (precision queueBits rootBits inputBits : Polynomial ℕ)
    (role : BodyRole) (queue root : IntegerBits) (output : List Bool)
    (hq : queue.digits.length ≤ queueBits.eval security) (hr : root.digits.length ≤ rootBits.eval security)
    (ho : output.length ≤ inputBits.eval security) :
    HeightBound (deviation security (precision.eval security) role queue root output).data.decode
      ((deviationHeightPolynomial precision queueBits rootBits inputBits).eval security) ∧
      (deviation security (precision.eval security) role queue root output).work ≤
        (deviationWorkPolynomial precision queueBits rootBits inputBits).eval security := by
  let first := shifted security (precision.eval security) role queue root output
  let second := mean security (precision.eval security) role queue output
  have hf := shifted_bounds security precision queueBits rootBits inputBits role queue root output hq hr ho
  have hs := mean_bounds security precision queueBits inputBits role queue output hq ho
  let H := (deviationOperandPolynomial precision queueBits rootBits inputBits).eval security
  have hH : H=(shiftedHeightPolynomial precision queueBits rootBits inputBits).eval security+
      (meanHeightPolynomial precision queueBits inputBits).eval security := by
    simp only [H,deviationOperandPolynomial,Polynomial.eval_add]
  have hw := difference_work first.data second.data H (hf.1.mono (by rw [hH]; omega))
    (hs.1.mono (by rw [hH]; omega))
  have wf : first.work ≤ (shiftedWorkPolynomial precision queueBits rootBits inputBits).eval security := hf.2
  have ws : second.work ≤ (meanWorkPolynomial precision queueBits inputBits).eval security := hs.2
  constructor
  · change HeightBound (difference first.data second.data).data.decode _
    rw [difference_value]
    simpa only [deviationHeightPolynomial,deviationOperandPolynomial,Polynomial.eval_add,Polynomial.eval_one,sub_eq_add_neg]
      using hf.1.add hs.1.neg
  · change first.work+second.work+(difference first.data second.data).work+3 ≤ _
    simp only [deviationWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      primitiveWorkPolynomial_eval]
    dsimp only [H] at hw
    omega

def meanDeviationOperandPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  meanHeightPolynomial precision queueBits inputBits+BinaryFirstInverseProgram.colorsPolynomial
def meanDeviationHeightPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*meanDeviationOperandPolynomial precision queueBits inputBits+1
def meanDeviationWorkPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    meanWorkPolynomial precision queueBits inputBits+
    3*primitiveWorkPolynomial (meanDeviationOperandPolynomial precision queueBits inputBits)+7

theorem meanDeviation_bounds (security : ℕ) (precision queueBits inputBits : Polynomial ℕ) (role : BodyRole)
    (queue : IntegerBits) (output : List Bool) (hq : queue.digits.length ≤ queueBits.eval security)
    (ho : output.length ≤ inputBits.eval security) :
    HeightBound (meanDeviation security (precision.eval security) role queue output).data.decode
      ((meanDeviationHeightPolynomial precision queueBits inputBits).eval security) ∧
      (meanDeviation security (precision.eval security) role queue output).work ≤
        (meanDeviationWorkPolynomial precision queueBits inputBits).eval security := by
  let modulus := PublicParameterProgram.modulus security
  let encoded := ofCounter modulus.count
  let reciprocal := RationalBits.inverse encoded.data
  let average := mean security (precision.eval security) role queue output
  let H := (meanDeviationOperandPolynomial precision queueBits inputBits).eval security
  have hH : H=(meanHeightPolynomial precision queueBits inputBits).eval security+
      BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    simp only [H,meanDeviationOperandPolynomial,Polynomial.eval_add]
  have hc : modulus.count ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := BinaryFirstInverseProgram.colors_bound security
  have he : HeightBound encoded.data.decode H := by
    rw [ofCounter_value]
    exact (HeightBound.nat_coarse modulus.count).mono (by rw [hH]; omega)
  have hr : HeightBound reciprocal.data.decode H := by rw [inverse_value]; exact he.inv
  have ha := mean_bounds security precision queueBits inputBits role queue output hq ho
  have hav : HeightBound average.data.decode H := ha.1.mono (by rw [hH]; omega)
  have wm : modulus.work ≤ PublicParameterProgram.workBound security := PublicParameterProgram.modulus_work security
  have we := (ofCounter_work modulus.count).trans
    (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2))
  have wi := RationalBits.inverse_work encoded.data H
  have wd := difference_work average.data reciprocal.data H hav hr
  change encoded.work ≤ 60*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 at we
  change reciprocal.work ≤ primitiveWorkBound H at wi
  have wa : average.work ≤ (meanWorkPolynomial precision queueBits inputBits).eval security := ha.2
  constructor
  · change HeightBound (difference average.data reciprocal.data).data.decode _
    rw [difference_value]
    rw [sub_eq_add_neg]
    apply (hav.add hr.neg).mono
    simp only [meanDeviationHeightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [H]
    omega
  · change modulus.work+encoded.work+reciprocal.work+average.work+(difference average.data reciprocal.data).work+5 ≤ _
    simp only [meanDeviationWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_ofNat,Polynomial.eval_one,primitiveWorkPolynomial_eval]
    rw [PublicParameterProgram.workPolynomial_eval]
    dsimp only [H] at wi wd
    omega

def densityInputHeightPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  deviationHeightPolynomial precision queueBits rootBits BinaryFirstInverseProgram.colorsPolynomial
def densityInputWorkPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    deviationWorkPolynomial precision queueBits rootBits BinaryFirstInverseProgram.colorsPolynomial+2
def meanDensityInputHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  meanDeviationHeightPolynomial precision queueBits BinaryFirstInverseProgram.colorsPolynomial
def meanDensityInputWorkPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    meanDeviationWorkPolynomial precision queueBits BinaryFirstInverseProgram.colorsPolynomial+2

theorem densityInput_bounds (security : ℕ) (precision queueBits rootBits : Polynomial ℕ) (role : BodyRole)
    (queue root : IntegerBits) (output : Fin (colors security))
    (hq : queue.digits.length ≤ queueBits.eval security) (hr : root.digits.length ≤ rootBits.eval security) :
    HeightBound (densityInput security (precision.eval security) role queue root output).data.decode
      ((densityInputHeightPolynomial precision queueBits rootBits).eval security) ∧
      (densityInput security (precision.eval security) role queue root output).work ≤
        (densityInputWorkPolynomial precision queueBits rootBits).eval security := by
  have ho := output.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : (canonicalCounter output.val).digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=output.val))).trans ho
  have h := deviation_bounds security precision queueBits rootBits BinaryFirstInverseProgram.colorsPolynomial
    role queue root (canonicalCounter output.val).digits hq hr hl
  have wc := (canonicalCounter_work output.val).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right ho 1) 2))
  constructor
  · exact h.1
  · change (canonicalCounter output.val).work+
      (deviation security (precision.eval security) role queue root (canonicalCounter output.val).digits).work+2 ≤ _
    simpa only [densityInputWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_ofNat,Polynomial.eval_one] using Nat.add_le_add_right (Nat.add_le_add wc h.2) 2

theorem meanDensityInput_bounds (security : ℕ) (precision queueBits : Polynomial ℕ) (role : BodyRole)
    (queue : IntegerBits) (output : Fin (colors security)) (hq : queue.digits.length ≤ queueBits.eval security) :
    HeightBound (meanDensityInput security (precision.eval security) role queue output).data.decode
      ((meanDensityInputHeightPolynomial precision queueBits).eval security) ∧
      (meanDensityInput security (precision.eval security) role queue output).work ≤
        (meanDensityInputWorkPolynomial precision queueBits).eval security := by
  have ho := output.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : (canonicalCounter output.val).digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=output.val))).trans ho
  have h := meanDeviation_bounds security precision queueBits BinaryFirstInverseProgram.colorsPolynomial
    role queue (canonicalCounter output.val).digits hq hl
  have wc := (canonicalCounter_work output.val).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right ho 1) 2))
  constructor
  · exact h.1
  · change (canonicalCounter output.val).work+
      (meanDeviation security (precision.eval security) role queue (canonicalCounter output.val).digits).work+2 ≤ _
    simpa only [meanDensityInputWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_ofNat,Polynomial.eval_one] using Nat.add_le_add_right (Nat.add_le_add wc h.2) 2

def firstDensityHeightPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (densityInputHeightPolynomial precision queueBits rootBits)
def firstDensityWorkPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (densityInputHeightPolynomial precision queueBits rootBits)
    (densityInputWorkPolynomial precision queueBits rootBits)
def meanDensityHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (meanDensityInputHeightPolynomial precision queueBits)
def meanDensityWorkPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (meanDensityInputHeightPolynomial precision queueBits)
    (meanDensityInputWorkPolynomial precision queueBits)

theorem firstDensity_bounds (security : ℕ) (precision queueBits rootBits : Polynomial ℕ) (role : BodyRole)
    (queue root : IntegerBits) (output : Fin (colors security))
    (hq : queue.digits.length ≤ queueBits.eval security) (hr : root.digits.length ≤ rootBits.eval security) :
    HeightBound (firstDensity security (precision.eval security) role queue root output).data.decode
      ((firstDensityHeightPolynomial precision queueBits rootBits).eval security) ∧
      (firstDensity security (precision.eval security) role queue root output).work ≤
        (firstDensityWorkPolynomial precision queueBits rootBits).eval security :=
  BinaryMassLiftInput.current_bounds security precision (densityInputHeightPolynomial precision queueBits rootBits)
    (densityInputWorkPolynomial precision queueBits rootBits) (densityInput security (precision.eval security) role queue root) output
    (fun color => (densityInput_bounds security precision queueBits rootBits role queue root color hq hr).1)
    (fun color => (densityInput_bounds security precision queueBits rootBits role queue root color hq hr).2)

theorem meanDensity_bounds (security : ℕ) (precision queueBits : Polynomial ℕ) (role : BodyRole)
    (queue : IntegerBits) (output : Fin (colors security)) (hq : queue.digits.length ≤ queueBits.eval security) :
    HeightBound (meanDensity security (precision.eval security) role queue output).data.decode
      ((meanDensityHeightPolynomial precision queueBits).eval security) ∧
      (meanDensity security (precision.eval security) role queue output).work ≤
        (meanDensityWorkPolynomial precision queueBits).eval security :=
  BinaryMassLiftInput.current_bounds security precision (meanDensityInputHeightPolynomial precision queueBits)
    (meanDensityInputWorkPolynomial precision queueBits) (meanDensityInput security (precision.eval security) role queue) output
    (fun color => (meanDensityInput_bounds security precision queueBits role queue color hq).1)
    (fun color => (meanDensityInput_bounds security precision queueBits role queue color hq).2)

end
end CurrentAFT.BinaryRootProfile

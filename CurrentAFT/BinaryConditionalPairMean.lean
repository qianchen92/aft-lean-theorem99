import CurrentAFT.BinaryConditionalPairProfile
import CurrentAFT.BinaryReferenceTables
import CurrentAFT.BinaryWindowAverage

/-! # The actual primary-averaged pair profile and its centered mass -/
namespace CurrentAFT.BinaryConditionalPairMean
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryConditionalPairProfile.current BinaryWindowAverage.sum
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def mean (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let refs := BinaryReferenceTables.current security bits
  let result := BinaryWindowAverage.sum refs.primary (fun primary => BinaryConditionalPairProfile.current security bits scalar primary output)
  ⟨result.data,modulus.work+refs.work+result.work+3⟩

theorem mean_value (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) :
    (mean security bits scalar output).data.decode=RationalConditionalPairProgram.pairMean security bits scalar.decode output.val := by
  simp only [mean,BinaryWindowAverage.sum_value,BinaryReferenceTables.primary_value,BinaryConditionalPairProfile.current_value,
    RationalConditionalPairProgram.pairMean]

def current (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  let averaged := mean security bits scalar output
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let two := ofCounter 2
  let reciprocal := RationalBits.inverse count.data
  let uniform := RationalBits.multiply two.data reciprocal.data
  let negative := RationalBits.negate uniform.data
  let result := RationalBits.add averaged.data negative.data
  ⟨result.data,averaged.work+modulus.work+count.work+two.work+reciprocal.work+uniform.work+negative.work+result.work+8⟩

theorem current_value (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) :
    (current security bits scalar output).data.decode=RationalConditionalPairProgram.centeredMean security bits scalar.decode output.val := by
  simp only [current,RationalBits.add_value,RationalBits.negate_value,RationalBits.multiply_value,inverse_value,
    ofCounter_value,mean_value,RationalConditionalPairProgram.centeredMean,RationalConditionalPairProgram.colors,Nat.cast_ofNat,div_eq_mul_inv,sub_eq_add_neg]

noncomputable section
noncomputable def meanHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(BinaryReferenceTables.heightPolynomial precision+
    BinaryConditionalPairProfile.heightPolynomial precision scalarBits+1)
noncomputable def meanWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryReferenceTables.currentWorkPolynomial precision+
    BinaryWindowAverage.sumWorkPolynomial BinaryFirstInverseProgram.colorsPolynomial (BinaryReferenceTables.heightPolynomial precision)
      (BinaryConditionalPairProfile.heightPolynomial precision scalarBits) (BinaryConditionalPairProfile.workPolynomial precision scalarBits)+3
noncomputable def operandPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  meanHeightPolynomial precision scalarBits+BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial precision scalarBits+1
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  meanWorkPolynomial precision scalarBits+PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    540+4*primitiveWorkPolynomial (operandPolynomial precision scalarBits)+8

theorem mean_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (output : Fin (colors security)) :
    HeightBound (mean security (precision.eval security) scalar output).data.decode
      ((meanHeightPolynomial precision scalarBits).eval security) ∧
    (mean security (precision.eval security) scalar output).work ≤ (meanWorkPolynomial precision scalarBits).eval security := by
  let refs := BinaryReferenceTables.current security (precision.eval security)
  have hr := BinaryReferenceTables.current_bounds security precision
  have h := BinaryWindowAverage.sum_bounds refs.primary
    (fun primary => BinaryConditionalPairProfile.current security (precision.eval security) scalar primary output)
    ((BinaryReferenceTables.heightPolynomial precision).eval security) ((BinaryConditionalPairProfile.heightPolynomial precision scalarBits).eval security)
    ((BinaryConditionalPairProfile.workPolynomial precision scalarBits).eval security) hr.1
    (fun primary => (BinaryConditionalPairProfile.current_bounds security precision scalarBits scalar hs primary output).1)
    (fun primary => (BinaryConditionalPairProfile.current_bounds security precision scalarBits scalar hs primary output).2)
  have hq := BinaryFirstInverseProgram.colors_bound security
  have wq := PublicParameterProgram.modulus_work security
  have wr : refs.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
  constructor
  · apply h.1.mono
    simp only [meanHeightPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one,BinaryWindowAverage.sumHeight]
    exact Nat.mul_le_mul_right _ hq
  · have hw := h.2.trans (BinaryWindowAverage.sumWork_mono hq le_rfl le_rfl le_rfl)
    change (PublicParameterProgram.modulus security).work+refs.work+(BinaryWindowAverage.sum _ _).work+3 ≤ _
    simp only [meanWorkPolynomial,BinaryWindowAverage.sumWorkPolynomial,BinaryWindowAverage.termWorkPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,primitiveWorkPolynomial_eval,
      PublicParameterProgram.workPolynomial_eval]
    change _ ≤ PublicParameterProgram.workBound security+(BinaryReferenceTables.currentWorkPolynomial precision).eval security+
      BinaryWindowAverage.sumWork (BinaryFirstInverseProgram.colorsPolynomial.eval security)
        ((BinaryReferenceTables.heightPolynomial precision).eval security) ((BinaryConditionalPairProfile.heightPolynomial precision scalarBits).eval security)
        ((BinaryConditionalPairProfile.workPolynomial precision scalarBits).eval security)+3
    dsimp only [refs] at hw wr ⊢
    omega

theorem current_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (output : Fin (colors security)) :
    HeightBound (current security (precision.eval security) scalar output).data.decode
      ((heightPolynomial precision scalarBits).eval security) ∧
    (current security (precision.eval security) scalar output).work ≤ (workPolynomial precision scalarBits).eval security := by
  let averaged := mean security (precision.eval security) scalar output
  let q := PublicParameterProgram.modulus security
  let count := ofCounter q.count
  let two := ofCounter 2
  let reciprocal := RationalBits.inverse count.data
  let uniform := RationalBits.multiply two.data reciprocal.data
  let negative := RationalBits.negate uniform.data
  let H := (operandPolynomial precision scalarBits).eval security
  have hH : H=(meanHeightPolynomial precision scalarBits).eval security+BinaryFirstInverseProgram.colorsPolynomial.eval security+2 := by
    simp only [H,operandPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  have hm := mean_bounds security precision scalarBits scalar hs output
  have hq := BinaryFirstInverseProgram.colors_bound security
  have hc : HeightBound count.data.decode (BinaryFirstInverseProgram.colorsPolynomial.eval security) := by
    rw [ofCounter_value]; exact (HeightBound.nat_coarse q.count).mono hq
  have ht : HeightBound two.data.decode 2 := by rw [ofCounter_value]; exact HeightBound.nat_coarse 2
  have hi : HeightBound reciprocal.data.decode (BinaryFirstInverseProgram.colorsPolynomial.eval security) := by rw [inverse_value]; exact hc.inv
  have hu : HeightBound uniform.data.decode (2+BinaryFirstInverseProgram.colorsPolynomial.eval security) := by
    rw [RationalBits.multiply_value]; exact ht.mul hi
  have hn : HeightBound negative.data.decode (2+BinaryFirstInverseProgram.colorsPolynomial.eval security) := by
    rw [RationalBits.negate_value]; exact hu.neg
  have wq := PublicParameterProgram.modulus_work security
  have wc : count.work ≤ 60*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 := (ofCounter_work q.count).trans (by gcongr)
  have wt : two.work ≤ 540 := by simpa using ofCounter_work 2
  have wi : reciprocal.work ≤ primitiveWorkBound H := inverse_work count.data H
  have wu := RationalBits.multiply_work two.data reciprocal.data H (ht.mono (by rw [hH]; omega)) (hi.mono (by rw [hH]; omega))
  have wn : negative.work ≤ primitiveWorkBound H := RationalBits.negate_work uniform.data H
  have wa := RationalBits.add_work averaged.data negative.data H (hm.1.mono (by rw [hH]; omega)) (hn.mono (by rw [hH]; omega))
  constructor
  · change HeightBound (RationalBits.add averaged.data negative.data).data.decode _
    rw [RationalBits.add_value]
    exact (hm.1.add hn).mono (by simp only [heightPolynomial,operandPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,Polynomial.eval_one]; omega)
  · change averaged.work+q.work+count.work+two.work+reciprocal.work+uniform.work+negative.work+(RationalBits.add averaged.data negative.data).work+8 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_one,PublicParameterProgram.workPolynomial_eval,primitiveWorkPolynomial_eval]
    change _ ≤ (meanWorkPolynomial precision scalarBits).eval security+PublicParameterProgram.workBound security+
      60*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2+540+4*primitiveWorkBound H+8
    dsimp only [averaged,q,count,two,reciprocal,uniform,negative] at hm wc wt wi wu wn wa wq ⊢
    omega

end
end CurrentAFT.BinaryConditionalPairMean

import CurrentAFT.BinaryRootControlRest
import CurrentAFT.BinaryFourPointPair
import CurrentAFT.BinaryRootWeightedScore

/-! Actual four-endpoint centered primary mass before scalar/root averaging. -/
namespace CurrentAFT.BinaryPrimaryFixedMass
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryFourPointPair.current BinaryRootControlRest.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (score : Vector RationalBits (colors security))
    (word : Vector (Fin (colors security)) 4) (primary center : Fin (colors security)) : RationalResult :=
  let references := BinaryReferenceTables.current security bits
  let p := readVector zero references.primary primary
  let b := BinaryRootWeightedScore.current security bits score primary center
  let pair := BinaryFourPointPair.current security bits primary scalar word
  let rest := BinaryRootControlRest.current security compensator attachment scalar center word
  let first := RationalBits.multiply p.value b.data
  let second := RationalBits.multiply first.data pair.data
  let final := RationalBits.multiply second.data rest.data
  ⟨final.data,references.work+p.work+b.work+pair.work+rest.work+first.work+second.work+final.work+8⟩

theorem term_value (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (score : Vector RationalBits (colors security))
    (word : Vector (Fin (colors security)) 4) (primary center : Fin (colors security)) :
    (term security bits compensator attachment scalar score word primary center).data.decode =
      RationalProposalProgram.primary security bits primary.val*RationalRootMassProgram.weightedScore security bits (BinaryCurrentPaired.scoreAt score) primary.val center.val*
        LocalPairProgram.current security bits primary.val scalar.decode (word.get 1).val (word.get 2).val*
          RationalRootMassProgram.controlRest security compensator.decode attachment.decode scalar.decode center.val
            (fun index => (word.get index).val) := by
  simp only [term, RationalBits.multiply_value, readVector_value, BinaryReferenceTables.primary_value,
    BinaryRootWeightedScore.current_value, BinaryFourPointPair.current_value, BinaryRootControlRest.current_value]

def fixedMass (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (score : Vector RationalBits (colors security))
    (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (fun primary => sumFin modulus.count (term security bits compensator attachment scalar score word primary))
  ⟨result.data,modulus.work+result.work+2⟩

theorem fixedMass_value (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (score : Vector RationalBits (colors security))
    (word : Vector (Fin (colors security)) 4) :
    (fixedMass security bits compensator attachment scalar score word).data.decode =
      RationalRootMassProgram.fixedMass security bits compensator.decode attachment.decode scalar.decode
        (BinaryCurrentPaired.scoreAt score) (fun index => (word.get index).val) := by
  simp only [fixedMass, sumFin_value, term_value, RationalRootMassProgram.fixedMass]


theorem fixedMass_value_of (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (score : Vector RationalBits (colors security)) (value : ℕ → ℚ)
    (hscore : ∀ index, (score.get index).decode=value index.val)
    (word : Vector (Fin (colors security)) 4) :
    (fixedMass security bits compensator attachment scalar score word).data.decode =
      RationalRootMassProgram.fixedMass security bits compensator.decode attachment.decode scalar.decode value
        (fun index => (word.get index).val) := by
  rw [fixedMass_value]
  unfold RationalRootMassProgram.fixedMass
  apply Finset.sum_congr rfl
  intro primary _
  apply Finset.sum_congr rfl
  intro center _
  have he : RationalRootMassProgram.weightedScore security bits (BinaryCurrentPaired.scoreAt score) primary.val center.val =
      RationalRootMassProgram.weightedScore security bits value primary.val center.val := by
    unfold RationalRootMassProgram.weightedScore RationalRootMassProgram.anchorScore
    rw [BinaryCurrentPaired.scoreAt_index,hscore primary]
    congr 2
    apply Finset.sum_congr rfl
    intro color _
    rw [BinaryCurrentPaired.scoreAt_index,hscore color]
  rw [he]

noncomputable section
noncomputable def termHeightPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.heightPolynomial precision+BinaryRootWeightedScore.heightPolynomial precision scoreBits+BinaryFourPointPair.heightPolynomial precision inputBits+
    BinaryRootControlRest.heightPolynomial inputBits
noncomputable def termWorkPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+3*BinaryFirstInverseProgram.colorsPolynomial+11+
    BinaryRootWeightedScore.workPolynomial precision scoreBits+
    BinaryFourPointPair.workPolynomial precision inputBits+BinaryRootControlRest.workPolynomial inputBits+
    3*primitiveWorkPolynomial (termHeightPolynomial precision inputBits scoreBits)

theorem term_bounds (security : ℕ) (precision inputBits scoreBits : Polynomial ℕ) (compensator attachment scalar : IntegerBits)
    (score : Vector RationalBits (colors security))
    (word : Vector (Fin (colors security)) 4) (primary center : Fin (colors security))
    (hc : compensator.digits.length ≤ inputBits.eval security)
    (ha : attachment.digits.length ≤ inputBits.eval security) (hs : scalar.digits.length ≤ inputBits.eval security)
    (hscore : ∀ index, HeightBound (score.get index).decode (scoreBits.eval security)) :
    HeightBound (term security (precision.eval security) compensator attachment scalar score word primary center).data.decode
      ((termHeightPolynomial precision inputBits scoreBits).eval security) ∧
      (term security (precision.eval security) compensator attachment scalar score word primary center).work ≤
        (termWorkPolynomial precision inputBits scoreBits).eval security := by
  let references := BinaryReferenceTables.current security (precision.eval security)
  let p := readVector zero references.primary primary
  let b := BinaryRootWeightedScore.current security (precision.eval security) score primary center
  let pair := BinaryFourPointPair.current security (precision.eval security) primary scalar word
  let rest := BinaryRootControlRest.current security compensator attachment scalar center word
  let first := RationalBits.multiply p.value b.data
  let second := RationalBits.multiply first.data pair.data
  let final := RationalBits.multiply second.data rest.data
  let R := (BinaryReferenceTables.heightPolynomial precision).eval security
  let P := (BinaryFourPointPair.heightPolynomial precision inputBits).eval security
  let C := (BinaryRootControlRest.heightPolynomial inputBits).eval security
  let B := (BinaryRootWeightedScore.heightPolynomial precision scoreBits).eval security
  let H := (termHeightPolynomial precision inputBits scoreBits).eval security
  have hH : H=R+B+P+C := by simp only [H, R, B, P, C, termHeightPolynomial, Polynomial.eval_add]
  have hr := BinaryReferenceTables.current_bounds security precision
  have hp : HeightBound p.value.decode R := by rw [readVector_value]; exact hr.1 primary
  have hwb := BinaryRootWeightedScore.current_bounds security precision scoreBits score primary center hscore
  change HeightBound b.data.decode B ∧ b.work ≤ _ at hwb
  have hb := hwb.1
  have hpair := BinaryFourPointPair.current_bounds security precision inputBits primary scalar word hs
  have hrest := BinaryRootControlRest.current_bounds security inputBits compensator attachment scalar center word hc ha hs
  change HeightBound pair.data.decode P ∧ pair.work ≤ _ at hpair
  change HeightBound rest.data.decode C ∧ rest.work ≤ _ at hrest
  have hfirst : HeightBound first.data.decode (R+B) := by rw [RationalBits.multiply_value]; exact (hp.mul hb).mono (by omega)
  have hsecond : HeightBound second.data.decode (R+B+P) := by rw [RationalBits.multiply_value]; exact hfirst.mul hpair.1
  have hfinal : HeightBound final.data.decode H := by rw [RationalBits.multiply_value]; exact (hsecond.mul hrest.1).mono (by rw [hH])
  have wf := RationalBits.multiply_work p.value b.data H (hp.mono (by rw [hH]; omega)) (hb.mono (by rw [hH]; omega))
  have ws := RationalBits.multiply_work first.data pair.data H (hfirst.mono (by rw [hH]; omega)) (hpair.1.mono (by rw [hH]; omega))
  have wt := RationalBits.multiply_work second.data rest.data H (hsecond.mono (by rw [hH]; omega)) (hrest.1.mono (by rw [hH]; omega))
  constructor
  · exact hfinal
  · have wp := readVector_work zero references.primary primary
    have wref : references.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
    have hq := BinaryFirstInverseProgram.colors_bound security
    change colors security ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security at hq
    change p.work ≤ 3*colors security+3 at wp
    change first.work ≤ primitiveWorkBound H at wf
    change second.work ≤ primitiveWorkBound H at ws
    change final.work ≤ primitiveWorkBound H at wt
    change references.work+p.work+b.work+pair.work+rest.work+first.work+second.work+final.work+8 ≤ _
    simp only [termWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, primitiveWorkPolynomial_eval]
    change _ ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security+3*BinaryFirstInverseProgram.colorsPolynomial.eval security+11+
      (BinaryRootWeightedScore.workPolynomial precision scoreBits).eval security+
      (BinaryFourPointPair.workPolynomial precision inputBits).eval security+(BinaryRootControlRest.workPolynomial inputBits).eval security+3*primitiveWorkBound H
    omega

noncomputable def innerHeightPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(termHeightPolynomial precision inputBits scoreBits+1)
noncomputable def innerWorkPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  Q*(termWorkPolynomial precision inputBits scoreBits+primitiveWorkPolynomial ((Q+1)*(termHeightPolynomial precision inputBits scoreBits+1))+2)+2
noncomputable def heightPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(innerHeightPolynomial precision inputBits scoreBits+1)
noncomputable def workPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  PublicParameterProgram.workPolynomial+Q*(innerWorkPolynomial precision inputBits scoreBits+
    primitiveWorkPolynomial ((Q+1)*(innerHeightPolynomial precision inputBits scoreBits+1))+2)+4

theorem fixedMass_bounds (security : ℕ) (precision inputBits scoreBits : Polynomial ℕ) (compensator attachment scalar : IntegerBits)
    (score : Vector RationalBits (colors security))
    (word : Vector (Fin (colors security)) 4) (hc : compensator.digits.length ≤ inputBits.eval security)
    (ha : attachment.digits.length ≤ inputBits.eval security) (hs : scalar.digits.length ≤ inputBits.eval security)
    (hscore : ∀ index, HeightBound (score.get index).decode (scoreBits.eval security)) :
    HeightBound (fixedMass security (precision.eval security) compensator attachment scalar score word).data.decode
      ((heightPolynomial precision inputBits scoreBits).eval security) ∧
      (fixedMass security (precision.eval security) compensator attachment scalar score word).work ≤
        (workPolynomial precision inputBits scoreBits).eval security := by
  let H := (termHeightPolynomial precision inputBits scoreBits).eval security
  let W := (termWorkPolynomial precision inputBits scoreBits).eval security
  let inner := fun primary => sumFin (colors security) (term security (precision.eval security) compensator attachment scalar score word primary)
  have hq := BinaryFirstInverseProgram.colors_bound security
  have ht := term_bounds security precision inputBits scoreBits compensator attachment scalar score word
  have hh (primary : Fin (colors security)) : HeightBound (inner primary).data.decode ((innerHeightPolynomial precision inputBits scoreBits).eval security) := by
    apply (sumFin_height (colors security) H _ (fun center => (ht primary center hc ha hs hscore).1)).mono
    simp only [innerHeightPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hq
  have hw (primary : Fin (colors security)) : (inner primary).work ≤ (innerWorkPolynomial precision inputBits scoreBits).eval security := by
    apply (sumFin_work (colors security) H W _ (fun center => (ht primary center hc ha hs hscore).1)
      (fun center => (ht primary center hc ha hs hscore).2)).trans
    simp only [innerWorkPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_one, primitiveWorkPolynomial_eval]
    dsimp only [H, W]
    gcongr
    exact primitiveWorkBound_mono (Nat.mul_le_mul_right _ (Nat.add_le_add_right hq 1))
  have hof := sumFin_height (colors security) ((innerHeightPolynomial precision inputBits scoreBits).eval security) inner hh
  have wow := sumFin_work (colors security) ((innerHeightPolynomial precision inputBits scoreBits).eval security)
    ((innerWorkPolynomial precision inputBits scoreBits).eval security) inner hh hw
  constructor
  · apply hof.mono
    simp only [heightPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hq
  · have wo : (sumFin (colors security) inner).work ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security*
        ((innerWorkPolynomial precision inputBits scoreBits).eval security+
          primitiveWorkBound ((BinaryFirstInverseProgram.colorsPolynomial.eval security+1)*
            ((innerHeightPolynomial precision inputBits scoreBits).eval security+1))+2)+2 := by
      apply wow.trans
      gcongr
      exact primitiveWorkBound_mono (Nat.mul_le_mul_right _ (Nat.add_le_add_right hq 1))
    have wm := PublicParameterProgram.modulus_work security
    change (PublicParameterProgram.modulus security).work+(sumFin (colors security) inner).work+2 ≤ _
    simp only [workPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_one,
      primitiveWorkPolynomial_eval, PublicParameterProgram.workPolynomial_eval]
    omega

end
end CurrentAFT.BinaryPrimaryFixedMass

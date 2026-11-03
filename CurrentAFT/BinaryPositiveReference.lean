import CurrentAFT.BinaryRootControlRest
import CurrentAFT.BinaryFourPointPair
import CurrentAFT.RationalPositiveReferenceProgram

/-! Actual four-endpoint positive reference mass before scalar/root averaging. -/
namespace CurrentAFT.BinaryPositiveReference
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryFourPointPair.current BinaryRootControlRest.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) (primary center : Fin (colors security)) : RationalResult :=
  let references := BinaryReferenceTables.current security bits
  let p := readVector zero references.primary primary
  let b := readVector zero references.center center
  let pair := BinaryFourPointPair.current security bits primary scalar word
  let rest := BinaryRootControlRest.current security compensator attachment scalar center word
  let first := RationalBits.multiply p.value b.value
  let second := RationalBits.multiply first.data pair.data
  let final := RationalBits.multiply second.data rest.data
  ⟨final.data,references.work+p.work+b.work+pair.work+rest.work+first.work+second.work+final.work+8⟩

theorem term_value (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) (primary center : Fin (colors security)) :
    (term security bits compensator attachment scalar word primary center).data.decode =
      RationalProposalProgram.primary security bits primary.val*RationalProposalProgram.center security bits center.val*
        LocalPairProgram.current security bits primary.val scalar.decode (word.get 1).val (word.get 2).val*
          RationalRootMassProgram.controlRest security compensator.decode attachment.decode scalar.decode center.val
            (fun index => (word.get index).val) := by
  simp only [term, RationalBits.multiply_value, readVector_value, BinaryReferenceTables.primary_value,
    BinaryReferenceTables.center_value, BinaryFourPointPair.current_value, BinaryRootControlRest.current_value]

def fixedMass (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (fun primary => sumFin modulus.count (term security bits compensator attachment scalar word primary))
  ⟨result.data,modulus.work+result.work+2⟩

theorem fixedMass_value (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) :
    (fixedMass security bits compensator attachment scalar word).data.decode =
      RationalPositiveReferenceProgram.fixedMass security bits compensator.decode attachment.decode scalar.decode
        (fun index => (word.get index).val) := by
  simp only [fixedMass, sumFin_value, term_value, RationalPositiveReferenceProgram.fixedMass]

noncomputable section
noncomputable def termHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryReferenceTables.heightPolynomial precision+BinaryFourPointPair.heightPolynomial precision inputBits+
    BinaryRootControlRest.heightPolynomial inputBits
noncomputable def termWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+6*BinaryFirstInverseProgram.colorsPolynomial+14+
    BinaryFourPointPair.workPolynomial precision inputBits+BinaryRootControlRest.workPolynomial inputBits+
    3*primitiveWorkPolynomial (termHeightPolynomial precision inputBits)

theorem term_bounds (security : ℕ) (precision inputBits : Polynomial ℕ) (compensator attachment scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) (primary center : Fin (colors security))
    (hc : compensator.digits.length ≤ inputBits.eval security)
    (ha : attachment.digits.length ≤ inputBits.eval security) (hs : scalar.digits.length ≤ inputBits.eval security) :
    HeightBound (term security (precision.eval security) compensator attachment scalar word primary center).data.decode
      ((termHeightPolynomial precision inputBits).eval security) ∧
      (term security (precision.eval security) compensator attachment scalar word primary center).work ≤
        (termWorkPolynomial precision inputBits).eval security := by
  let references := BinaryReferenceTables.current security (precision.eval security)
  let p := readVector zero references.primary primary
  let b := readVector zero references.center center
  let pair := BinaryFourPointPair.current security (precision.eval security) primary scalar word
  let rest := BinaryRootControlRest.current security compensator attachment scalar center word
  let first := RationalBits.multiply p.value b.value
  let second := RationalBits.multiply first.data pair.data
  let final := RationalBits.multiply second.data rest.data
  let R := (BinaryReferenceTables.heightPolynomial precision).eval security
  let P := (BinaryFourPointPair.heightPolynomial precision inputBits).eval security
  let C := (BinaryRootControlRest.heightPolynomial inputBits).eval security
  let H := (termHeightPolynomial precision inputBits).eval security
  have hH : H=2*R+P+C := by simp only [H, R, P, C, termHeightPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  have hr := BinaryReferenceTables.current_bounds security precision
  have hp : HeightBound p.value.decode R := by rw [readVector_value]; exact hr.1 primary
  have hb : HeightBound b.value.decode R := by rw [readVector_value]; exact hr.2.1 center
  have hpair := BinaryFourPointPair.current_bounds security precision inputBits primary scalar word hs
  have hrest := BinaryRootControlRest.current_bounds security inputBits compensator attachment scalar center word hc ha hs
  change HeightBound pair.data.decode P ∧ pair.work ≤ _ at hpair
  change HeightBound rest.data.decode C ∧ rest.work ≤ _ at hrest
  have hfirst : HeightBound first.data.decode (2*R) := by rw [RationalBits.multiply_value]; exact (hp.mul hb).mono (by omega)
  have hsecond : HeightBound second.data.decode (2*R+P) := by rw [RationalBits.multiply_value]; exact hfirst.mul hpair.1
  have hfinal : HeightBound final.data.decode H := by rw [RationalBits.multiply_value]; exact (hsecond.mul hrest.1).mono (by rw [hH])
  have wf := RationalBits.multiply_work p.value b.value H (hp.mono (by rw [hH]; omega)) (hb.mono (by rw [hH]; omega))
  have ws := RationalBits.multiply_work first.data pair.data H (hfirst.mono (by rw [hH]; omega)) (hpair.1.mono (by rw [hH]; omega))
  have wt := RationalBits.multiply_work second.data rest.data H (hsecond.mono (by rw [hH]; omega)) (hrest.1.mono (by rw [hH]; omega))
  constructor
  · exact hfinal
  · have wp := readVector_work zero references.primary primary
    have wb := readVector_work zero references.center center
    have wref : references.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
    have hq := BinaryFirstInverseProgram.colors_bound security
    change colors security ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security at hq
    change p.work ≤ 3*colors security+3 at wp
    change b.work ≤ 3*colors security+3 at wb
    change first.work ≤ primitiveWorkBound H at wf
    change second.work ≤ primitiveWorkBound H at ws
    change final.work ≤ primitiveWorkBound H at wt
    change references.work+p.work+b.work+pair.work+rest.work+first.work+second.work+final.work+8 ≤ _
    simp only [termWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, primitiveWorkPolynomial_eval]
    change _ ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security+6*BinaryFirstInverseProgram.colorsPolynomial.eval security+14+
      (BinaryFourPointPair.workPolynomial precision inputBits).eval security+(BinaryRootControlRest.workPolynomial inputBits).eval security+3*primitiveWorkBound H
    omega

noncomputable def innerHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(termHeightPolynomial precision inputBits+1)
noncomputable def innerWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  Q*(termWorkPolynomial precision inputBits+primitiveWorkPolynomial ((Q+1)*(termHeightPolynomial precision inputBits+1))+2)+2
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(innerHeightPolynomial precision inputBits+1)
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  PublicParameterProgram.workPolynomial+Q*(innerWorkPolynomial precision inputBits+
    primitiveWorkPolynomial ((Q+1)*(innerHeightPolynomial precision inputBits+1))+2)+4

theorem fixedMass_bounds (security : ℕ) (precision inputBits : Polynomial ℕ) (compensator attachment scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) (hc : compensator.digits.length ≤ inputBits.eval security)
    (ha : attachment.digits.length ≤ inputBits.eval security) (hs : scalar.digits.length ≤ inputBits.eval security) :
    HeightBound (fixedMass security (precision.eval security) compensator attachment scalar word).data.decode
      ((heightPolynomial precision inputBits).eval security) ∧
      (fixedMass security (precision.eval security) compensator attachment scalar word).work ≤
        (workPolynomial precision inputBits).eval security := by
  let H := (termHeightPolynomial precision inputBits).eval security
  let W := (termWorkPolynomial precision inputBits).eval security
  let inner := fun primary => sumFin (colors security) (term security (precision.eval security) compensator attachment scalar word primary)
  have hq := BinaryFirstInverseProgram.colors_bound security
  have ht := term_bounds security precision inputBits compensator attachment scalar word
  have hh (primary : Fin (colors security)) : HeightBound (inner primary).data.decode ((innerHeightPolynomial precision inputBits).eval security) := by
    apply (sumFin_height (colors security) H _ (fun center => (ht primary center hc ha hs).1)).mono
    simp only [innerHeightPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hq
  have hw (primary : Fin (colors security)) : (inner primary).work ≤ (innerWorkPolynomial precision inputBits).eval security := by
    apply (sumFin_work (colors security) H W _ (fun center => (ht primary center hc ha hs).1)
      (fun center => (ht primary center hc ha hs).2)).trans
    simp only [innerWorkPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_one, primitiveWorkPolynomial_eval]
    dsimp only [H, W]
    gcongr
    exact primitiveWorkBound_mono (Nat.mul_le_mul_right _ (Nat.add_le_add_right hq 1))
  have hof := sumFin_height (colors security) ((innerHeightPolynomial precision inputBits).eval security) inner hh
  have wow := sumFin_work (colors security) ((innerHeightPolynomial precision inputBits).eval security)
    ((innerWorkPolynomial precision inputBits).eval security) inner hh hw
  constructor
  · apply hof.mono
    simp only [heightPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hq
  · have wo : (sumFin (colors security) inner).work ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security*
        ((innerWorkPolynomial precision inputBits).eval security+
          primitiveWorkBound ((BinaryFirstInverseProgram.colorsPolynomial.eval security+1)*
            ((innerHeightPolynomial precision inputBits).eval security+1))+2)+2 := by
      apply wow.trans
      gcongr
      exact primitiveWorkBound_mono (Nat.mul_le_mul_right _ (Nat.add_le_add_right hq 1))
    have wm := PublicParameterProgram.modulus_work security
    change (PublicParameterProgram.modulus security).work+(sumFin (colors security) inner).work+2 ≤ _
    simp only [workPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_one,
      primitiveWorkPolynomial_eval, PublicParameterProgram.workPolynomial_eval]
    omega

end
end CurrentAFT.BinaryPositiveReference

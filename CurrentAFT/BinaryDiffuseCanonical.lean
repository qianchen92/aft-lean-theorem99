import CurrentAFT.BinaryCanonicalPair
import CurrentAFT.BinaryDiffusePairLeaf

/-! # Both literal canonicalizations of the actual fair diffuse pair -/
namespace CurrentAFT.BinaryDiffuseCanonical
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryCanonicalPair.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def seed (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryCanonicalPair.current modulus.count (BinaryDiffusePairLeaf.safeReference security)
    (BinaryDiffusePairLeaf.safePair security bits scalar) first second
  ⟨result.data,modulus.work+result.work+2⟩

theorem seed_value (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) :
    (seed security bits scalar first second).data.decode=RationalDiffuseResidualProgram.seed security bits scalar.decode first.val second.val := by
  change (BinaryCanonicalPair.current _ _ _ _ _).data.decode=_
  rw [BinaryCanonicalPair.current_value,RationalDiffuseResidualProgram.seed,rationalCanonicalPairProgram_fin]
  simp only [rationalCanonicalPair,BinaryDiffusePairLeaf.safeReference_value,BinaryDiffusePairLeaf.safePair_value]

def uniform (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryCanonicalPair.current modulus.count (BinaryDiffusePairLeaf.uniformReference security)
    (BinaryDiffusePairLeaf.pair security bits scalar) first second
  ⟨result.data,modulus.work+result.work+2⟩

theorem uniform_value (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) :
    (uniform security bits scalar first second).data.decode=RationalDiffuseResidualProgram.uniformCanonical security bits scalar.decode first.val second.val := by
  change (BinaryCanonicalPair.current _ _ _ _ _).data.decode=_
  rw [BinaryCanonicalPair.current_value,RationalDiffuseResidualProgram.uniformCanonical,rationalCanonicalPairProgram_fin]
  simp only [rationalCanonicalPair,BinaryDiffusePairLeaf.uniformReference_value,BinaryDiffusePairLeaf.pair_value]

noncomputable section
noncomputable def seedHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCanonicalPair.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial BinaryDiffusePairLeaf.safeHeightPolynomial
    (BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits)
noncomputable def seedWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    BinaryCanonicalPair.workPolynomial BinaryFirstInverseProgram.colorsPolynomial BinaryDiffusePairLeaf.safeHeightPolynomial
      (BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits) BinaryDiffusePairLeaf.safeWorkPolynomial
      (BinaryDiffusePairLeaf.safePairWorkPolynomial precision scalarBits)+2
noncomputable def uniformHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCanonicalPair.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial BinaryFirstInverseProgram.colorsPolynomial
    (BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits)
noncomputable def uniformWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    BinaryCanonicalPair.workPolynomial BinaryFirstInverseProgram.colorsPolynomial BinaryFirstInverseProgram.colorsPolynomial
      (BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits) BinaryDiffusePairLeaf.uniformWorkPolynomial
      (BinaryDiffusePairLeaf.pairWorkPolynomial precision scalarBits)+2

theorem seed_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (first second : Fin (colors security)) :
    HeightBound (seed security (precision.eval security) scalar first second).data.decode
      ((seedHeightPolynomial precision scalarBits).eval security) ∧
    (seed security (precision.eval security) scalar first second).work ≤ (seedWorkPolynomial precision scalarBits).eval security := by
  have h := BinaryCanonicalPair.current_bounds (colors security) (BinaryDiffusePairLeaf.safeReference security)
    (BinaryDiffusePairLeaf.safePair security (precision.eval security) scalar) first second
    (BinaryDiffusePairLeaf.safeHeightPolynomial.eval security) ((BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits).eval security)
    (BinaryDiffusePairLeaf.safeWorkPolynomial.eval security) ((BinaryDiffusePairLeaf.safePairWorkPolynomial precision scalarBits).eval security)
    (fun output => (BinaryDiffusePairLeaf.safeReference_bounds security output).1)
    (fun first second => (BinaryDiffusePairLeaf.safePair_bounds security precision scalarBits scalar hs first second).1)
    (fun output => (BinaryDiffusePairLeaf.safeReference_bounds security output).2)
    (fun first second => (BinaryDiffusePairLeaf.safePair_bounds security precision scalarBits scalar hs first second).2)
  have hq := BinaryFirstInverseProgram.colors_bound security
  have wq := PublicParameterProgram.modulus_work security
  constructor
  · apply h.1.mono
    rw [seedHeightPolynomial,BinaryCanonicalPair.heightPolynomial_eval]
    exact BinaryCanonicalPair.height_mono hq
  · have hw := h.2.trans (BinaryCanonicalPair.work_mono hq)
    change (PublicParameterProgram.modulus security).work+(BinaryCanonicalPair.current _ _ _ _ _).work+2 ≤ _
    simp only [seedWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,BinaryCanonicalPair.workPolynomial_eval]
    rw [PublicParameterProgram.workPolynomial_eval]
    exact Nat.add_le_add_right (Nat.add_le_add wq hw) 2

theorem uniform_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (first second : Fin (colors security)) :
    HeightBound (uniform security (precision.eval security) scalar first second).data.decode
      ((uniformHeightPolynomial precision scalarBits).eval security) ∧
    (uniform security (precision.eval security) scalar first second).work ≤ (uniformWorkPolynomial precision scalarBits).eval security := by
  have h := BinaryCanonicalPair.current_bounds (colors security) (BinaryDiffusePairLeaf.uniformReference security)
    (BinaryDiffusePairLeaf.pair security (precision.eval security) scalar) first second
    (BinaryFirstInverseProgram.colorsPolynomial.eval security) ((BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits).eval security)
    (BinaryDiffusePairLeaf.uniformWorkPolynomial.eval security) ((BinaryDiffusePairLeaf.pairWorkPolynomial precision scalarBits).eval security)
    (fun output => (BinaryDiffusePairLeaf.uniformReference_bounds security output).1)
    (fun first second => (BinaryDiffusePairLeaf.pair_bounds security precision scalarBits scalar hs first second).1)
    (fun output => (BinaryDiffusePairLeaf.uniformReference_bounds security output).2)
    (fun first second => (BinaryDiffusePairLeaf.pair_bounds security precision scalarBits scalar hs first second).2)
  have hq := BinaryFirstInverseProgram.colors_bound security
  have wq := PublicParameterProgram.modulus_work security
  constructor
  · apply h.1.mono
    rw [uniformHeightPolynomial,BinaryCanonicalPair.heightPolynomial_eval]
    exact BinaryCanonicalPair.height_mono hq
  · have hw := h.2.trans (BinaryCanonicalPair.work_mono hq)
    change (PublicParameterProgram.modulus security).work+(BinaryCanonicalPair.current _ _ _ _ _).work+2 ≤ _
    simp only [uniformWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,BinaryCanonicalPair.workPolynomial_eval]
    rw [PublicParameterProgram.workPolynomial_eval]
    exact Nat.add_le_add_right (Nat.add_le_add wq hw) 2

end
end CurrentAFT.BinaryDiffuseCanonical

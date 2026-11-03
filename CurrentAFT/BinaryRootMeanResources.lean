import CurrentAFT.BinaryRootPreProfileResources

/-! # Materialized root profiles and exact binary convolution resources -/
namespace CurrentAFT.BinaryRootProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current BinaryPaletteLookup.current
  BinaryShiftedSafeProfile.current PublicParameterProgram.modulus BinaryActivationProgram.cutoff
  BinaryRootConvolution.current IntegerBits.residue signedAdd
noncomputable section

def keyBitsPolynomial (rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  rootBits+inputBits+BinaryFirstInverseProgram.colorsPolynomial+1
def keyWorkPolynomial (rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    20*(rootBits+inputBits)+8+60*(rootBits+inputBits+BinaryFirstInverseProgram.colorsPolynomial+2)^2+14

theorem key_bounds (security : ℕ) (rootBits inputBits : Polynomial ℕ) (root : IntegerBits) (output : List Bool)
    (hr : root.digits.length ≤ rootBits.eval security) (ho : output.length ≤ inputBits.eval security) :
    (key security root output).digits.length ≤ (keyBitsPolynomial rootBits inputBits).eval security ∧
      (key security root output).work ≤ (keyWorkPolynomial rootBits inputBits).eval security := by
  let modulus := PublicParameterProgram.modulus security
  let code := canonicalCounter modulus.count
  let difference := signedAdd false (!root.negative) output root.digits
  let residue := IntegerBits.residue ⟨difference.negative,difference.digits⟩ code.digits
  let Q := BinaryFirstInverseProgram.colorsPolynomial.eval security
  let R := rootBits.eval security
  let I := inputBits.eval security
  have hq : modulus.count ≤ Q := BinaryFirstInverseProgram.colors_bound security
  have hc : code.digits.length ≤ Q := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := modulus.count))).trans hq
  have hd : difference.digits.length ≤ R+I+1 := (signedAdd_length _ _ _ _).trans (by omega)
  have hl : residue.digits.length ≤ R+I+Q+1 := (IntegerBits.residue_length _ _).trans (by dsimp only; omega)
  have wm : modulus.work ≤ PublicParameterProgram.workBound security := PublicParameterProgram.modulus_work security
  have wc : code.work ≤ 50*(Q+1)^2 := (canonicalCounter_work modulus.count).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  have wd : difference.work ≤ 20*(R+I)+8 := (signedAdd_work _ _ _ _).trans (by omega)
  have wr : residue.work ≤ 60*(R+I+Q+2)^2+10 := (IntegerBits.residue_work _ _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (by dsimp only; omega) 2)) 10)
  constructor
  · simpa only [key, keyBitsPolynomial, Polynomial.eval_add, Polynomial.eval_one] using hl
  · change modulus.work+code.work+difference.work+residue.work+4 ≤ _
    simp only [keyWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    rw [PublicParameterProgram.workPolynomial_eval]
    change _ ≤ PublicParameterProgram.workBound security+50*(Q+1)^2+20*(R+I)+8+60*(R+I+Q+2)^2+14
    omega

def shiftedHeightPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  preRootHeightPolynomial precision queueBits (keyBitsPolynomial rootBits inputBits)
def shiftedWorkPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  keyWorkPolynomial rootBits inputBits+preRootWorkPolynomial precision queueBits (keyBitsPolynomial rootBits inputBits)+2

theorem shifted_bounds (security : ℕ) (precision queueBits rootBits inputBits : Polynomial ℕ)
    (role : BodyRole) (queue root : IntegerBits) (output : List Bool)
    (hq : queue.digits.length ≤ queueBits.eval security) (hr : root.digits.length ≤ rootBits.eval security)
    (ho : output.length ≤ inputBits.eval security) :
    HeightBound (shifted security (precision.eval security) role queue root output).data.decode
      ((shiftedHeightPolynomial precision queueBits rootBits inputBits).eval security) ∧
      (shifted security (precision.eval security) role queue root output).work ≤
        (shiftedWorkPolynomial precision queueBits rootBits inputBits).eval security := by
  have hk := key_bounds security rootBits inputBits root output hr ho
  have hp := preRoot_bounds security precision queueBits (keyBitsPolynomial rootBits inputBits) role queue
    (key security root output).digits hq hk.1
  constructor
  · exact hp.1
  · change (key security root output).work+
      (preRoot security (precision.eval security) role queue (key security root output).digits).work+2 ≤ _
    simpa only [shiftedWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat] using
      Nat.add_le_add_right (Nat.add_le_add hk.2 hp.2) 2

def profileHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  preRootHeightPolynomial precision queueBits BinaryFirstInverseProgram.colorsPolynomial
def profileWorkPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    preRootWorkPolynomial precision queueBits BinaryFirstInverseProgram.colorsPolynomial+2

theorem profileAt_bounds (security : ℕ) (precision queueBits : Polynomial ℕ) (role : BodyRole)
    (queue : IntegerBits) (output : Fin (colors security)) (hq : queue.digits.length ≤ queueBits.eval security) :
    HeightBound (profileAt security (precision.eval security) role queue output).data.decode
      ((profileHeightPolynomial precision queueBits).eval security) ∧
      (profileAt security (precision.eval security) role queue output).work ≤
        (profileWorkPolynomial precision queueBits).eval security := by
  have ho := output.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : (canonicalCounter output.val).digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output.val))).trans ho
  have hp := preRoot_bounds security precision queueBits BinaryFirstInverseProgram.colorsPolynomial role queue
    (canonicalCounter output.val).digits hq hl
  have wc := (canonicalCounter_work output.val).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right ho 1) 2))
  constructor
  · exact hp.1
  · change (canonicalCounter output.val).work+
      (preRoot security (precision.eval security) role queue (canonicalCounter output.val).digits).work+2 ≤ _
    simpa only [profileWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one] using Nat.add_le_add_right (Nat.add_le_add wc hp.2) 2

def meanHeightPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootConvolution.heightPolynomial precision inputBits (profileHeightPolynomial precision queueBits)
def meanWorkPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    BinaryFirstInverseProgram.colorsPolynomial*(profileWorkPolynomial precision queueBits+2)+2+
    BinaryRootConvolution.workPolynomial precision inputBits (profileHeightPolynomial precision queueBits)+3

theorem mean_bounds (security : ℕ) (precision queueBits inputBits : Polynomial ℕ) (role : BodyRole)
    (queue : IntegerBits) (output : List Bool) (hq : queue.digits.length ≤ queueBits.eval security)
    (ho : output.length ≤ inputBits.eval security) :
    HeightBound (mean security (precision.eval security) role queue output).data.decode
      ((meanHeightPolynomial precision queueBits inputBits).eval security) ∧
      (mean security (precision.eval security) role queue output).work ≤
        (meanWorkPolynomial precision queueBits inputBits).eval security := by
  let modulus := PublicParameterProgram.modulus security
  let profile := buildArray modulus.count (profileAt security (precision.eval security) role queue)
  have hp (color : Fin (colors security)) := profileAt_bounds security precision queueBits role queue color hq
  have hentries (color : Fin (colors security)) : HeightBound (profile.data.get color).decode
      ((profileHeightPolynomial precision queueBits).eval security) := by rw [buildArray_get]; exact (hp color).1
  have hc := BinaryRootConvolution.current_bounds security precision inputBits (profileHeightPolynomial precision queueBits)
    profile.data output ho hentries
  have wp := (buildArray_work (colors security) ((profileWorkPolynomial precision queueBits).eval security)
    (profileAt security (precision.eval security) role queue) (fun color => (hp color).2)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (BinaryFirstInverseProgram.colors_bound security)) 2)
  have wm := PublicParameterProgram.modulus_work security
  constructor
  · exact hc.1
  · change modulus.work+profile.work+(BinaryRootConvolution.current security (precision.eval security) profile.data output).work+3 ≤ _
    simp only [meanWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    rw [PublicParameterProgram.workPolynomial_eval]
    change profile.work ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security*
      ((profileWorkPolynomial precision queueBits).eval security+2)+2 at wp
    change modulus.work ≤ PublicParameterProgram.workBound security at wm
    omega

end
end CurrentAFT.BinaryRootProfile

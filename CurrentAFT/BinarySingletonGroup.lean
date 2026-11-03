import CurrentAFT.BinaryRootSingletonResources
import CurrentAFT.RationalRootGroupProgram

/-! # Stored root-source reads for the two singleton group roles -/
namespace CurrentAFT.BinarySingletonGroup
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits order : ℕ) (programs : List (Entry order)) (role : BodyRole)
    (queue : IntegerBits) (source : Vector (Fin (colors security)) 3) : CoefficientProgram order :=
  fun arity colors centers =>
    let root := readVector (BinaryFirstFamily.first security) source 0
    let code := canonicalCounter root.value.val
    let result := BinaryRootSingleton.current security bits order programs role queue ⟨false,code.digits⟩ arity colors centers
    ⟨result.value,root.work+code.work+result.work+3⟩

noncomputable section
open scoped Classical

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (role : BodyRole)
    (queue : IntegerBits) (source : Vector (Fin (colors security)) 3)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (current security bits order programs role queue source arity colors centers).value.decode =
      BinaryRootSingleton.normalized security order
        (RationalSingletonProgram.current security bits order role queue.decode (source.get 0).val)
          arity colors.get centers.get := by
  simp only [current,readVector_value,BinaryRootSingleton.current_value security bits order programs hcorrect hcomplete,
    IntegerBits.decode,signedValue,Bool.false_eq_true,if_false,canonicalCounter_value]

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootSingleton.heightPolynomial order programs precision queueBits BinaryFirstInverseProgram.colorsPolynomial
def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryRootSingleton.workPolynomial order programs precision queueBits BinaryFirstInverseProgram.colorsPolynomial+15

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ)
    (role : BodyRole) (queue : IntegerBits) (source : Vector (Fin (colors security)) 3)
    (hq : queue.digits.length ≤ queueBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (current security (precision.eval security) order programs role queue source arity colors centers).value.decode
      ((heightPolynomial order programs precision queueBits).eval security) ∧
      (current security (precision.eval security) order programs role queue source arity colors centers).work ≤
        (workPolynomial order programs precision queueBits).eval security := by
  let root := readVector (BinaryFirstFamily.first security) source 0
  let code := canonicalCounter root.value.val
  have hr := root.value.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : code.digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=root.value.val))).trans hr
  have h := BinaryRootSingleton.current_bounds security order programs precision queueBits BinaryFirstInverseProgram.colorsPolynomial
    role queue ⟨false,code.digits⟩ hq hl arity colors centers hc hd
  have wr : root.work≤12 := readVector_work (BinaryFirstFamily.first security) source 0
  have wc : code.work≤50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 :=
    (canonicalCounter_work root.value.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 2))
  constructor
  · exact h.1
  · change root.work+code.work+
      (BinaryRootSingleton.current security (precision.eval security) order programs role queue ⟨false,code.digits⟩ arity colors centers).work+3 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega

end
end CurrentAFT.BinarySingletonGroup

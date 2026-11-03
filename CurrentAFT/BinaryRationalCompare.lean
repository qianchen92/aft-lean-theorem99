import AFT.BinarySignedComparison
import AFT.BinaryFiniteArithmetic

/-! # Rational guards from actual cross products and signed comparisons -/
namespace CurrentAFT.BinaryRationalCompare
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def le (first second : RationalBits) : CountedValue Bool :=
  let left := BinaryArithmetic.multiply first.numerator second.denominator
  let right := BinaryArithmetic.multiply second.numerator first.denominator
  let result := signedLe first.negative second.negative left.digits right.digits
  ⟨result.value, left.work + right.work + result.work + 3⟩

theorem le_value (first second : RationalBits) :
    (le first second).value = true ↔ first.decode ≤ second.decode := by
  have cross (sign : Bool) (top bottom : List Bool) :
      signedValue sign (BinaryArithmetic.multiply top bottom).digits =
        signedValue sign top*(value bottom:ℤ) := by
    cases sign <;> simp [signedValue, BinaryArithmetic.multiply_value]
  simp only [le, signedLe_value, cross]
  rw [decode_fraction, decode_fraction,
    div_le_div_iff₀ (by exact_mod_cast first.denominator_positive) (by exact_mod_cast second.denominator_positive)]
  constructor <;> intro h <;> exact_mod_cast h

def workBound (height : ℕ) : ℕ := 40*(2*height+3)^2+72*(height+1)+21

theorem le_work (first second : RationalBits) (height : ℕ)
    (hf : HeightBound first.decode height) (hs : HeightBound second.decode height) :
    (le first second).work ≤ workBound height := by
  rcases lengths_of_height first height hf with ⟨hfn, hfd⟩
  rcases lengths_of_height second height hs with ⟨hsn, hsd⟩
  let left := BinaryArithmetic.multiply first.numerator second.denominator
  let right := BinaryArithmetic.multiply second.numerator first.denominator
  have hl : left.digits.length ≤ 3*(height+1) := (BinaryArithmetic.multiply_length _ _).trans (by omega)
  have hr : right.digits.length ≤ 3*(height+1) := (BinaryArithmetic.multiply_length _ _).trans (by omega)
  have wl : left.work ≤ 20*(2*height+3)^2 :=
    (BinaryArithmetic.multiply_work first.numerator second.denominator).trans
      (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2))
  have wr : right.work ≤ 20*(2*height+3)^2 :=
    (BinaryArithmetic.multiply_work second.numerator first.denominator).trans
      (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2))
  have ws := signedLe_work first.negative second.negative left.digits right.digits
  change left.work + right.work + (signedLe first.negative second.negative left.digits right.digits).work + 3 ≤ _
  unfold workBound
  omega

def maximum (first second : RationalBits) : RationalResult :=
  let test := le first second
  ⟨if test.value then second else first, test.work+3⟩

theorem maximum_value (first second : RationalBits) :
    (maximum first second).data.decode = max first.decode second.decode := by
  unfold maximum
  dsimp only
  by_cases h : (le first second).value = true
  · rw [if_pos h, max_eq_right ((le_value _ _).mp h)]
  · rw [if_neg h, max_eq_left (le_of_not_ge (fun hle => h ((le_value _ _).mpr hle)))]

theorem maximum_height (first second : RationalBits) (height : ℕ)
    (hf : HeightBound first.decode height) (hs : HeightBound second.decode height) :
    HeightBound (maximum first second).data.decode height := by
  unfold maximum
  dsimp only
  split <;> assumption

theorem maximum_work (first second : RationalBits) (height : ℕ)
    (hf : HeightBound first.decode height) (hs : HeightBound second.decode height) :
    (maximum first second).work ≤ workBound height+3 := Nat.add_le_add_right (le_work _ _ _ hf hs) 3

noncomputable def workPolynomial (height : Polynomial ℕ) : Polynomial ℕ := 40*(2*height+3)^2+72*(height+1)+21
theorem workPolynomial_eval (height : Polynomial ℕ) (security : ℕ) :
    (workPolynomial height).eval security = workBound (height.eval security) := by
  simp only [workPolynomial, workBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one]

end CurrentAFT.BinaryRationalCompare

import AFT.BinarySliceProbability
import AFT.ActualConditionalPairProgram
import AFT.BinarySeriesPolynomials

/-! # Boolean-list evaluation of one genuine averaged trimmed pair

No rational probability is encoded as advice: the anchor membership,
shifted slice, actual slice denominator and final product are computed
by binary operations on the supplied integer representations.
-/
namespace CurrentAFT.BinaryTrimmedPair
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalNumerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem signed_negate (sign : Bool) (digits : List Bool) :
    signedValue (!sign) digits = -signedValue sign digits := by
  cases sign <;> simp [signedValue]

def pairShift (colors first second : List Bool) : SignedResult :=
  let total := add false first second
  let last := signedAdd false true colors [true]
  let result := signedAdd false (!last.negative) total.digits last.digits
  ⟨result.negative, result.digits, total.work + last.work + result.work + 3⟩

theorem pairShift_value (colors first second : List Bool) :
    signedValue (pairShift colors first second).negative (pairShift colors first second).digits =
      (value first : ℤ) + value second - ((value colors : ℤ) - 1) := by
  unfold pairShift
  rw [signedAdd_value, signed_negate, signedAdd_value]
  simp only [signedValue, Bool.false_eq_true, if_false, if_true, BinaryArithmetic.add_value,
    Bool.toNat_false, Nat.add_zero, Int.natCast_add]
  norm_num [value]
  ring_nf

theorem pairShift_bounds (colors first second : List Bool) (bits : ℕ)
    (hb : 1 ≤ bits) (hq : colors.length ≤ bits) (hf : first.length ≤ bits) (hs : second.length ≤ bits) :
    (pairShift colors first second).digits.length ≤ bits+2 ∧
      (pairShift colors first second).work ≤ 60*(bits+1) := by
  have ht := add_length first second false
  have hw := add_work first second false
  have hl := signedAdd_length false true colors [true]
  have hwl := signedAdd_work false true colors [true]
  have hr := signedAdd_length false (!(signedAdd false true colors [true]).negative)
    (add false first second).digits (signedAdd false true colors [true]).digits
  have hwr := signedAdd_work false (!(signedAdd false true colors [true]).negative)
    (add false first second).digits (signedAdd false true colors [true]).digits
  have hm : max first.length second.length ≤ bits := max_le hf hs
  have hqm : max colors.length [true].length ≤ bits := max_le hq (by simpa using hb)
  have hrm : max (add false first second).digits.length (signedAdd false true colors [true]).digits.length ≤ bits+1 := by
    omega
  simp only [pairShift]
  constructor <;> omega

def pair (startSign sourceSign : Bool) (colors width start source first second : List Bool) : RationalResult :=
  let shift := pairShift colors first second
  let argument := signedAdd shift.negative sourceSign shift.digits source
  let anchor := binaryIntervalProbability startSign argument.negative start width argument.digits
  let slice := binarySliceProbability false false shift.negative false colors [true] shift.digits first
  let result := RationalBits.multiply anchor.data slice.data
  ⟨result.data, shift.work + argument.work + anchor.work + slice.work + result.work + 4⟩

theorem pair_value (startSign sourceSign : Bool) (colors width start source first second : List Bool) :
    (pair startSign sourceSign colors width start source first second).data.decode =
      AFT.V7Calibration.averagedPairProgram (value colors) 1 (signedValue startSign start)
        (signedValue sourceSign source) (value width) (value first) (value second) := by
  unfold pair
  rw [RationalBits.multiply_value, binaryIntervalProbability_value,
    binarySliceProbability_value, signedAdd_value, pairShift_value]
  norm_num [signedValue, value]
  rfl

def pairWork (bits : ℕ) : ℕ :=
  60*(bits+1) + 20*(bits+2)+8 + binaryIntervalProbabilityWork (bits+3) +
    binarySliceProbabilityWork (bits+2) + RationalBits.primitiveWorkBound (bits+5) + 4

theorem pair_work (startSign sourceSign : Bool) (colors width start source first second : List Bool) (bits : ℕ)
    (hb : 1 ≤ bits) (hq : colors.length ≤ bits) (hw : width.length ≤ bits)
    (hstart : start.length ≤ bits) (hsource : source.length ≤ bits)
    (hf : first.length ≤ bits) (hs : second.length ≤ bits) :
    (pair startSign sourceSign colors width start source first second).work ≤ pairWork bits := by
  let shift := pairShift colors first second
  let argument := signedAdd shift.negative sourceSign shift.digits source
  let anchor := binaryIntervalProbability startSign argument.negative start width argument.digits
  let slice := binarySliceProbability false false shift.negative false colors [true] shift.digits first
  have hshift := pairShift_bounds colors first second bits hb hq hf hs
  have wshift : shift.work ≤ 60*(bits+1) := hshift.2
  have hm : max shift.digits.length source.length ≤ bits+2 := max_le hshift.1 (by omega)
  have hargument : argument.digits.length ≤ bits+3 := (signedAdd_length _ _ _ _).trans (by omega)
  have wargument : argument.work ≤ 20*(bits+2)+8 := (signedAdd_work _ _ _ _).trans (by omega)
  have wanchor : anchor.work ≤ binaryIntervalProbabilityWork (bits+3) :=
    binaryIntervalProbability_work _ _ _ _ _ _ (by omega) (by omega) hargument
  have wslice : slice.work ≤ binarySliceProbabilityWork (bits+2) :=
    binarySliceProbability_work _ _ _ _ _ _ _ _ _ (by omega) (by simp) hshift.1 (by omega)
  have hanchor : HeightBound anchor.data.decode (bits+3) :=
    binaryIntervalProbability_height _ _ _ _ _ _ (by omega)
  have hslice : HeightBound slice.data.decode (bits+5) := by
    exact binarySliceProbability_height _ _ _ _ _ _ _ _ (bits+2) (by omega) (by simp) hshift.1
  have wproduct := RationalBits.multiply_work anchor.data slice.data (bits+5)
    (hanchor.mono (by omega)) hslice
  change shift.work + argument.work + anchor.work + slice.work +
    (RationalBits.multiply anchor.data slice.data).work + 4 ≤ _
  unfold pairWork
  omega

theorem pair_height (startSign sourceSign : Bool) (colors width start source first second : List Bool) (bits : ℕ)
    (hb : 1 ≤ bits) (hq : colors.length ≤ bits) (hw : width.length ≤ bits)
    (hf : first.length ≤ bits) (hs : second.length ≤ bits) :
    HeightBound (pair startSign sourceSign colors width start source first second).data.decode (2*bits+8) := by
  let shift := pairShift colors first second
  let argument := signedAdd shift.negative sourceSign shift.digits source
  let anchor := binaryIntervalProbability startSign argument.negative start width argument.digits
  let slice := binarySliceProbability false false shift.negative false colors [true] shift.digits first
  have hshift := pairShift_bounds colors first second bits hb hq hf hs
  have hanchor : HeightBound anchor.data.decode (bits+3) :=
    binaryIntervalProbability_height _ _ _ _ _ _ (by omega)
  have hslice : HeightBound slice.data.decode (bits+5) :=
    binarySliceProbability_height _ _ _ _ _ _ _ _ (bits+2) (by omega) (by simp) hshift.1
  change HeightBound (RationalBits.multiply anchor.data slice.data).data.decode _
  rw [RationalBits.multiply_value]
  exact (hanchor.mul hslice).mono (by omega)

noncomputable def pairWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  60*(bits+1) + 20*(bits+2)+8 +
    (200*(bits+5) + RationalBits.primitiveWorkPolynomial (bits+3)) +
    (100*(bits+4) + 20*(bits+4)+11 + 200*(bits+7) + RationalBits.primitiveWorkPolynomial (bits+5)) +
    RationalBits.primitiveWorkPolynomial (bits+5) + 4

theorem pairWorkPolynomial_eval (bits : Polynomial ℕ) (security : ℕ) :
    (pairWorkPolynomial bits).eval security = pairWork (bits.eval security) := by
  simp only [pairWorkPolynomial, pairWork, binaryIntervalProbabilityWork, binarySliceProbabilityWork,
    binaryEndpointProbabilityWork, RationalBits.primitiveWorkPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring_nf

end CurrentAFT.BinaryTrimmedPair

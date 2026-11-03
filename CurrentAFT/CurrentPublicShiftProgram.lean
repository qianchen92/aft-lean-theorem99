import CurrentAFT.CurrentFlagChartDraw
import CurrentAFT.PublicParameterProgram
import AFT.BinaryIntegerData

/-! Actual public-shift encoding by counter comparisons and signed binary arithmetic. -/

namespace CurrentAFT.CurrentPublicShiftProgram

open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 500000

def encode : ℤ → CountedValue IntegerBits
  | .ofNat value =>
    let bits := canonicalCounter value
    ⟨⟨false, bits.digits⟩, bits.work + 1⟩
  | .negSucc value =>
    let bits := canonicalCounter (value + 1)
    ⟨⟨true, bits.digits⟩, bits.work + 1⟩

theorem encode_value (value : ℤ) : (encode value).value.decode = value := by
  cases value with
  | ofNat value => simp [encode, IntegerBits.decode, signedValue, canonicalCounter_value]
  | negSucc value =>
    simp [encode, IntegerBits.decode, signedValue, canonicalCounter_value]
    omega

theorem encode_length (value : ℤ) : (encode value).value.digits.length ≤ value.natAbs := by
  cases value with
  | ofNat value =>
    change (canonicalCounter value).digits.length ≤ value
    rw [canonicalCounter_length]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := _))
  | negSucc value =>
    change (canonicalCounter (value + 1)).digits.length ≤ value + 1
    rw [canonicalCounter_length]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := _))

theorem encode_work (value : ℤ) : (encode value).work ≤ 50 * (value.natAbs + 1) ^ 2 + 1 := by
  cases value <;> simpa only [encode, Int.natAbs_natCast, Int.natAbs_negSucc] using
    Nat.add_le_add_right (canonicalCounter_work _) 1

def direction (modulus primary : ℕ) (coin : Bool) : CountedValue Bool :=
  let doubled := doubleCounter primary
  let boundary := differenceCounter modulus 1
  let below := lessCounter doubled.count boundary.count
  let above := lessCounter boundary.count doubled.count
  ⟨if below.value then false else if above.value then true else coin,
    doubled.work + boundary.work + below.work + above.work + 3⟩

theorem direction_value (modulus primary : ℕ) (coin : Bool) :
    (direction modulus primary coin).value =
      if 2 * primary < modulus - 1 then false else if modulus - 1 < 2 * primary then true else coin := by
  simp only [direction, doubleCounter_value, differenceCounter_value, lessCounter_value]

theorem direction_work (modulus primary : ℕ) (coin : Bool) :
    (direction modulus primary coin).work ≤ 15 * primary + 8 * modulus + 9 := by
  have hb := lessCounter_work (2 * primary) (modulus - 1)
  have ha := lessCounter_work (modulus - 1) (2 * primary)
  have hd := differenceCounter_work modulus 1
  simp only [direction, doubleCounter_value, differenceCounter_value, doubleCounter_work]
  omega

def program (modulus width primary index : ℕ) (coin : Bool) (blurFirst blurSecond : ℤ) : CountedValue IntegerBits :=
  let sign := direction modulus primary coin
  let offset := addCounter width index
  let bits := canonicalCounter offset.count
  let signedOffset : IntegerBits := ⟨!sign.value, bits.digits⟩
  let first := encode blurFirst
  let second := encode blurSecond
  let blur := IntegerBits.subtract first.value second.value
  let result := IntegerBits.add signedOffset blur.value
  ⟨result.value, sign.work + offset.work + bits.work + first.work + second.work + blur.work + result.work + 7⟩

theorem program_value (modulus width primary index : ℕ) (coin : Bool) (blurFirst blurSecond : ℤ) :
    (program modulus width primary index coin blurFirst blurSecond).value.decode =
      (if (direction modulus primary coin).value then ((width + index : ℕ) : ℤ) else -((width + index : ℕ) : ℤ)) +
        blurFirst - blurSecond := by
  simp only [program]
  rw [IntegerBits.add_value, IntegerBits.subtract_value, encode_value, encode_value]
  simp only [IntegerBits.decode, signedValue, canonicalCounter_value, addCounter_value]
  cases (direction modulus primary coin).value <;> simp <;> ring

def programWork (modulus width primary index firstSize secondSize : ℕ) : ℕ :=
  (15 * primary + 8 * modulus + 9) + (2 * width + 1) + 50 * (width + index + 1) ^ 2 +
    (50 * (firstSize + 1) ^ 2 + 1) + (50 * (secondSize + 1) ^ 2 + 1) +
    (20 * (firstSize + secondSize) + 13) + (20 * (width + index + firstSize + secondSize + 1) + 9) + 7

theorem program_work (modulus width primary index : ℕ) (coin : Bool) (blurFirst blurSecond : ℤ) :
    (program modulus width primary index coin blurFirst blurSecond).work ≤
      programWork modulus width primary index blurFirst.natAbs blurSecond.natAbs := by
  have hs := direction_work modulus primary coin
  have ho := addCounter_work width index
  have hc := canonicalCounter_work (width + index)
  have h1 := encode_work blurFirst
  have h2 := encode_work blurSecond
  have hb := IntegerBits.subtract_work (encode blurFirst).value (encode blurSecond).value
  have hl := IntegerBits.subtract_length (encode blurFirst).value (encode blurSecond).value
  have hf := encode_length blurFirst
  have he := encode_length blurSecond
  have hbits : (canonicalCounter (width + index)).digits.length ≤ width + index := by
    rw [canonicalCounter_length]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := _))
  have hr := IntegerBits.add_work
    (⟨!(direction modulus primary coin).value, (canonicalCounter (width + index)).digits⟩ : IntegerBits)
    (IntegerBits.subtract (encode blurFirst).value (encode blurSecond).value).value
  change _ ≤ 20 * max (canonicalCounter (width + index)).digits.length
    (IntegerBits.subtract (encode blurFirst).value (encode blurSecond).value).value.digits.length + 9 at hr
  have hmax1 : max (encode blurFirst).value.digits.length (encode blurSecond).value.digits.length ≤
      blurFirst.natAbs + blurSecond.natAbs := max_le (by omega) (by omega)
  have hmax2 : max (canonicalCounter (width + index)).digits.length
      (IntegerBits.subtract (encode blurFirst).value (encode blurSecond).value).value.digits.length ≤
      width + index + blurFirst.natAbs + blurSecond.natAbs + 1 := max_le (by omega) (by omega)
  simp only [program, addCounter_value, programWork]
  omega

def current (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) : CountedValue IntegerBits :=
  let modulus := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := powerCounter base.count 48
  let result := program modulus.count width.count primary.val seed.anchorIndex.val seed.coin seed.blur.1.val seed.blur.2.val
  ⟨result.value, modulus.work + base.work + width.work + result.work + 3⟩

theorem current_value (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) :
    (current security primary seed).value.decode = ActualPublicLegCharge.publicShift security primary seed := by
  simp only [current, program_value, PublicParameterProgram.modulus_value, addCounter_value,
    powerCounter_value, direction_value, ActualPublicLegCharge.publicShift, ActualPublicLegCharge.signedOffset,
    InwardAnchor.positiveDirection, InwardAnchor.offset, Parameters.anchorWidth, Parameters.scale, Parameters.base,
    ← pow_mul, Nat.cast_add]

end CurrentAFT.CurrentPublicShiftProgram

import AFT.BinaryBitTape
import AFT.BinaryRationalFloor

/-! Actual binary dyadic rounding. The exponential-size ticket count is
stored as a linear-length binary list and is never expanded into unary. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def dyadicPower (bits : ℕ) : RationalResult :=
  let digits := powerTwoDigits bits
  let result := ofNat digits.digits
  ⟨result.data,digits.work+result.work+2⟩

theorem dyadicPower_value (bits : ℕ) : (dyadicPower bits).data.decode=(2 : ℚ)^bits := by
  simp only [dyadicPower,ofNat_value,powerTwoDigits_value,Nat.cast_pow,Nat.cast_ofNat]

theorem dyadicPower_work (bits : ℕ) : (dyadicPower bits).work=6*bits+13 := by
  simp only [dyadicPower,ofNat_work,powerTwoDigits_length,powerTwoDigits_work]
  omega

theorem dyadicPower_height (bits : ℕ) : HeightBound (dyadicPower bits).data.decode bits := by
  rw [dyadicPower_value]
  have hh : HeightBound ((2^bits : ℕ) : ℚ) bits := HeightBound.of_nat le_rfl
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh

def dyadicFloor (input : RationalBits) (bits : ℕ) : Result :=
  let power := dyadicPower bits
  let scaled := multiply power.data input
  let floored := floorNatural scaled.data
  ⟨floored.digits,power.work+scaled.work+floored.work+3⟩

theorem dyadicFloor_value (input : RationalBits) (bits : ℕ) :
    value (dyadicFloor input bits).digits=⌊(2 : ℚ)^bits*input.decode⌋₊ := by
  simp only [dyadicFloor,floorNatural_value,multiply_value,dyadicPower_value]

theorem dyadicFloor_height (input : RationalBits) (height bits : ℕ)
    (hh : HeightBound input.decode height) :
    (dyadicFloor input bits).digits.length≤ bits+height+1 := by
  have hs : HeightBound (multiply (dyadicPower bits).data input).data.decode (bits+height) := by
    rw [multiply_value]
    exact (dyadicPower_height bits).mul hh
  exact floorNatural_length_of_height _ _ hs

def dyadicFloorWork (height bits : ℕ) : ℕ :=
  1000*(bits+height+2)^2+primitiveWorkBound (bits+height)+6*bits+16

theorem dyadicFloor_work (input : RationalBits) (height bits : ℕ)
    (hh : HeightBound input.decode height) : (dyadicFloor input bits).work≤ dyadicFloorWork height bits := by
  have hs : HeightBound (multiply (dyadicPower bits).data input).data.decode (bits+height) := by
    rw [multiply_value]
    exact (dyadicPower_height bits).mul hh
  have wm := multiply_work (dyadicPower bits).data input (bits+height)
    ((dyadicPower_height bits).mono (Nat.le_add_right _ _)) (hh.mono (Nat.le_add_left _ _))
  have wf := floorNatural_work (multiply (dyadicPower bits).data input).data (bits+height) hs
  simp only [dyadicFloor,dyadicPower_work,dyadicFloorWork]
  omega

end AFT.BinaryArithmetic.RationalBits

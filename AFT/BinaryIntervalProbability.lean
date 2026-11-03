import AFT.BinarySignedComparison
import AFT.BinaryFiniteArithmetic
import AFT.CountedPrimaryProgram

/-! Interval probabilities on signed binary endpoints. Comparisons,
endpoint addition, reciprocal, and zero branch are fully executable. -/
namespace AFT.BinaryArithmetic
open RationalNumerics V7Calibration RationalBits

/-- Uniform mass on [start,start+width). -/
def binaryIntervalProbability (startSign colorSign : Bool) (start width color : List Bool) : RationalResult :=
  let upper := signedAdd startSign false start width
  let lowerTest := signedLe startSign colorSign start color
  let upperTest := signedLe upper.negative colorSign upper.digits color
  if lowerTest.value && !upperTest.value then
    let denominator := RationalBits.ofNat width
    let result := RationalBits.inverse denominator.data
    ⟨result.data,upper.work+lowerTest.work+upperTest.work+denominator.work+result.work+6⟩
  else ⟨RationalBits.zero,upper.work+lowerTest.work+upperTest.work+3⟩

theorem binaryIntervalProbability_value (startSign colorSign : Bool) (start width color : List Bool) :
    (binaryIntervalProbability startSign colorSign start width color).data.decode=
      intervalProbabilityProgram (signedValue startSign start) (value width) (signedValue colorSign color) := by
  have upperValue := signedAdd_value startSign false start width
  have hc : ((signedLe startSign colorSign start color).value &&
      !(signedLe (signedAdd startSign false start width).negative colorSign
        (signedAdd startSign false start width).digits color).value)=true ↔
      signedValue startSign start≤signedValue colorSign color ∧
      signedValue colorSign color<signedValue startSign start+(value width : ℤ) := by
    simp only [Bool.and_eq_true,Bool.not_eq_true']
    rw [signedLe_value,←Bool.not_eq_true,signedLe_value,not_le,upperValue]
    rfl
  rw [←countedIntervalProbability_value]
  by_cases h : ((signedLe startSign colorSign start color).value &&
      !(signedLe (signedAdd startSign false start width).negative colorSign
        (signedAdd startSign false start width).digits color).value)=true
  · simp only [countedIntervalProbability,binaryIntervalProbability,if_pos h,
      if_pos (hc.mp h),RationalBits.inverse_value,RationalBits.ofNat_value]
  · simp only [countedIntervalProbability,binaryIntervalProbability,if_neg h,
      if_neg (mt hc.mpr h),RationalBits.zero_value]

def binaryIntervalProbabilityWork (bits : ℕ) : ℕ :=
  200*(bits+2)+RationalBits.primitiveWorkBound bits

theorem binaryIntervalProbability_work (startSign colorSign : Bool) (start width color : List Bool)
    (bits : ℕ) (hs : start.length≤bits) (hw : width.length≤bits) (hc : color.length≤bits) :
    (binaryIntervalProbability startSign colorSign start width color).work≤binaryIntervalProbabilityWork bits := by
  have hu := signedAdd_work startSign false start width
  have hul := signedAdd_length startSign false start width
  have hl := signedLe_work startSign colorSign start color
  have ht := signedLe_work (signedAdd startSign false start width).negative colorSign
    (signedAdd startSign false start width).digits color
  have hi := RationalBits.inverse_work (RationalBits.ofNat width).data bits
  have hm1 : max start.length width.length≤bits := max_le hs hw
  have hm2 : max start.length color.length≤bits := max_le hs hc
  have hm3 : max (signedAdd startSign false start width).digits.length color.length≤bits+1 := by omega
  simp only [binaryIntervalProbability,binaryIntervalProbabilityWork,RationalBits.ofNat_work]
  split_ifs <;> dsimp only <;> omega

theorem binaryIntervalProbability_height (startSign colorSign : Bool) (start width color : List Bool)
    (bits : ℕ) (hw : width.length≤bits) :
    HeightBound (binaryIntervalProbability startSign colorSign start width color).data.decode bits := by
  have hwidth : HeightBound (value width : ℚ) bits :=
    HeightBound.of_nat ((value_lt width).le.trans (Nat.pow_le_pow_right (by decide) hw))
  simp only [binaryIntervalProbability]
  split_ifs
  · simpa only [RationalBits.inverse_value,RationalBits.ofNat_value] using hwidth.inv
  · simpa only [RationalBits.zero_value] using HeightBound.zero.mono (Nat.zero_le bits)

end AFT.BinaryArithmetic

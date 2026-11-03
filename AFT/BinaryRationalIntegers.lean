import AFT.BinaryRationalData

/-! Integer-to-rational constructors read an existing signed binary input.
They never convert an opaque arbitrary-precision natural in one step. -/
namespace AFT.BinaryArithmetic.RationalBits

def ofInt (negative : Bool) (digits : List Bool) : RationalResult :=
  let normalized := normalize digits
  ⟨{negative := negative,numerator := normalized.digits,denominator := [true]
    numerator_normal := by dsimp only [normalized];rw [normalize_length,normalize_value]
    denominator_normal := by decide
    denominator_positive := by decide
    coprime := by simp [value]},normalized.work+3⟩

def ofNat (digits : List Bool) : RationalResult := ofInt false digits

theorem ofInt_value (negative : Bool) (digits : List Bool) :
    (ofInt negative digits).data.decode=(signedValue negative digits : ℚ) := by
  rw [decode_fraction]
  simp only [ofInt,signedValue,normalize_value,value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero,
    Nat.cast_one,div_one]

theorem ofNat_value (digits : List Bool) : (ofNat digits).data.decode=(value digits : ℚ) := by
  simp [ofNat,ofInt_value,signedValue]

theorem ofInt_work (negative : Bool) (digits : List Bool) :
    (ofInt negative digits).work=4*digits.length+5 := by
  simp only [ofInt,normalize_work]

theorem ofNat_work (digits : List Bool) : (ofNat digits).work=4*digits.length+5 := ofInt_work ..

end AFT.BinaryArithmetic.RationalBits

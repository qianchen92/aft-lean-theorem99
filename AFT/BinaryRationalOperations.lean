import AFT.BinarySignedAddition

/-! Executable arithmetic on canonical rational bit strings. -/
namespace AFT.BinaryArithmetic
namespace RationalBits

def zero : RationalBits := ⟨false,[],[true],by decide,by decide,by decide,by decide⟩

def negate (input : RationalBits) : RationalResult :=
  ⟨{input with negative := !input.negative},2⟩

def inverse (input : RationalBits) : RationalResult :=
  if hz : input.numerator=[] then ⟨zero,2⟩ else
    ⟨{negative := input.negative,numerator := input.denominator,denominator := input.numerator
      numerator_normal := input.denominator_normal,denominator_normal := input.numerator_normal
      denominator_positive := by
        by_contra hn
        have hh : value input.numerator=0 := by omega
        have hl := input.numerator_normal
        rw [hh,Nat.size_zero] at hl
        exact hz (List.length_eq_zero_iff.mp hl)
      coprime := input.coprime.symm},2⟩

def multiply (first second : RationalBits) : RationalResult :=
  let top := BinaryArithmetic.multiply first.numerator second.numerator
  let bottom := BinaryArithmetic.multiply first.denominator second.denominator
  let result := reduce (first.negative ^^ second.negative) top.digits bottom.digits (by
    rw [BinaryArithmetic.multiply_value]
    exact Nat.mul_pos first.denominator_positive second.denominator_positive)
  ⟨result.data,top.work+bottom.work+result.work+3⟩

def add (first second : RationalBits) : RationalResult :=
  let left := BinaryArithmetic.multiply first.numerator second.denominator
  let right := BinaryArithmetic.multiply second.numerator first.denominator
  let top := signedAdd first.negative second.negative left.digits right.digits
  let bottom := BinaryArithmetic.multiply first.denominator second.denominator
  let result := reduce top.negative top.digits bottom.digits (by
    rw [BinaryArithmetic.multiply_value]
    exact Nat.mul_pos first.denominator_positive second.denominator_positive)
  ⟨result.data,left.work+right.work+top.work+bottom.work+result.work+4⟩

@[simp] theorem zero_value : zero.decode=0 := by decide

theorem negate_value (input : RationalBits) : (negate input).data.decode= -input.decode := by
  rw [decode_fraction,decode_fraction]
  simp only [negate,signedValue]
  cases input.negative <;> simp [neg_div]

theorem inverse_value (input : RationalBits) : (inverse input).data.decode=input.decode⁻¹ := by
  simp only [inverse]
  split <;> rename_i hz
  · have hn : input.decode=0 := by rw [decode_fraction];simp [signedValue,hz,value]
    simp [hn]
  · rw [decode_fraction,decode_fraction]
    simp only [signedValue]
    cases input.negative <;> simp [inv_div,neg_div]

theorem multiply_value (first second : RationalBits) :
    (multiply first second).data.decode=first.decode*second.decode := by
  simp only [multiply,reduce_value,signedValue,BinaryArithmetic.multiply_value]
  rw [decode_fraction,decode_fraction]
  cases first.negative <;> cases second.negative <;>
    simp [signedValue,Nat.cast_mul,Int.cast_mul,div_mul_div_comm]

theorem add_value (first second : RationalBits) : (add first second).data.decode=first.decode+second.decode := by
  simp only [add,reduce_value,signedAdd_value,Int.cast_add]
  rw [decode_fraction,decode_fraction]
  simp only [signedValue,BinaryArithmetic.multiply_value,Nat.cast_mul]
  have hd1 : (value first.denominator : ℚ) ≠ 0 := by exact_mod_cast first.denominator_positive.ne'
  have hd2 : (value second.denominator : ℚ) ≠ 0 := by exact_mod_cast second.denominator_positive.ne'
  cases first.negative <;> cases second.negative <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,Int.cast_natCast,Int.cast_neg,Int.cast_mul] <;> field_simp

def primitiveWorkBound (bits : ℕ) : ℕ := 10000000*(bits+2)^3

theorem negate_work (input : RationalBits) (bits : ℕ) :
    (negate input).work ≤ primitiveWorkBound bits := by
  have hh : 1 ≤ (bits+2)^3 := Nat.one_le_pow _ _ (by omega)
  simp only [negate,primitiveWorkBound]
  omega

theorem inverse_work (input : RationalBits) (bits : ℕ) :
    (inverse input).work ≤ primitiveWorkBound bits := by
  have hh : 1 ≤ (bits+2)^3 := Nat.one_le_pow _ _ (by omega)
  simp only [inverse,primitiveWorkBound]
  split <;> change 2 ≤ _ <;> omega

theorem multiply_work (first second : RationalBits) (bits : ℕ)
    (hf : AFT.RationalNumerics.HeightBound first.decode bits)
    (hs : AFT.RationalNumerics.HeightBound second.decode bits) :
    (multiply first second).work ≤ primitiveWorkBound bits := by
  obtain ⟨hfn,hfd⟩ := lengths_of_height first bits hf
  obtain ⟨hsn,hsd⟩ := lengths_of_height second bits hs
  have ht := BinaryArithmetic.multiply_work first.numerator second.numerator
  have hb := BinaryArithmetic.multiply_work first.denominator second.denominator
  have htl := BinaryArithmetic.multiply_length first.numerator second.numerator
  have hbl := BinaryArithmetic.multiply_length first.denominator second.denominator
  have hr := reduce_work (first.negative ^^ second.negative)
    (BinaryArithmetic.multiply first.numerator second.numerator).digits
    (BinaryArithmetic.multiply first.denominator second.denominator).digits (by
      rw [BinaryArithmetic.multiply_value];exact Nat.mul_pos first.denominator_positive second.denominator_positive)
  have htop : first.numerator.length+second.numerator.length+1 ≤ 2*(bits+2) := by omega
  have hbot : first.denominator.length+second.denominator.length+1 ≤ 2*(bits+2) := by omega
  have hraw : (BinaryArithmetic.multiply first.numerator second.numerator).digits.length+
      (BinaryArithmetic.multiply first.denominator second.denominator).digits.length+1 ≤ 6*(bits+2) := by omega
  simp only [multiply,primitiveWorkBound]
  have hone : 1 ≤ bits+2 := by omega
  nlinarith [Nat.pow_le_pow_left htop 2,Nat.pow_le_pow_left hbot 2,Nat.pow_le_pow_left hraw 3,
    Nat.mul_le_mul_left ((bits+2)^2) hone]

theorem add_work (first second : RationalBits) (bits : ℕ)
    (hf : AFT.RationalNumerics.HeightBound first.decode bits)
    (hs : AFT.RationalNumerics.HeightBound second.decode bits) :
    (add first second).work ≤ primitiveWorkBound bits := by
  obtain ⟨hfn,hfd⟩ := lengths_of_height first bits hf
  obtain ⟨hsn,hsd⟩ := lengths_of_height second bits hs
  let left := BinaryArithmetic.multiply first.numerator second.denominator
  let right := BinaryArithmetic.multiply second.numerator first.denominator
  let top := signedAdd first.negative second.negative left.digits right.digits
  let bottom := BinaryArithmetic.multiply first.denominator second.denominator
  have hl := BinaryArithmetic.multiply_work first.numerator second.denominator
  have hr := BinaryArithmetic.multiply_work second.numerator first.denominator
  have hb := BinaryArithmetic.multiply_work first.denominator second.denominator
  have hll : left.digits.length ≤ 3*(bits+1) := by
    have hh := BinaryArithmetic.multiply_length first.numerator second.denominator;dsimp only [left];omega
  have hrl : right.digits.length ≤ 3*(bits+1) := by
    have hh := BinaryArithmetic.multiply_length second.numerator first.denominator;dsimp only [right];omega
  have hbl : bottom.digits.length ≤ 3*(bits+1) := by
    have hh := BinaryArithmetic.multiply_length first.denominator second.denominator;dsimp only [bottom];omega
  have htw := signedAdd_work first.negative second.negative left.digits right.digits
  have htl := signedAdd_length first.negative second.negative left.digits right.digits
  have hd : 0 < value bottom.digits := by
    dsimp only [bottom];rw [BinaryArithmetic.multiply_value]
    exact Nat.mul_pos first.denominator_positive second.denominator_positive
  have hred := reduce_work top.negative top.digits bottom.digits hd
  have hmax : max left.digits.length right.digits.length ≤ 3*(bits+1) := by omega
  have hraw : top.digits.length+bottom.digits.length+1 ≤ 6*(bits+2) := by dsimp only [top];omega
  have hleft : first.numerator.length+second.denominator.length+1 ≤ 2*(bits+2) := by omega
  have hright : second.numerator.length+first.denominator.length+1 ≤ 2*(bits+2) := by omega
  have hbottom : first.denominator.length+second.denominator.length+1 ≤ 2*(bits+2) := by omega
  change left.work+right.work+top.work+bottom.work+(reduce top.negative top.digits bottom.digits hd).work+4 ≤ _
  change left.work ≤ _ at hl
  change right.work ≤ _ at hr
  change bottom.work ≤ _ at hb
  change top.work ≤ _ at htw
  simp only [primitiveWorkBound]
  have hone : 1 ≤ bits+2 := by omega
  nlinarith [Nat.pow_le_pow_left hleft 2,Nat.pow_le_pow_left hright 2,Nat.pow_le_pow_left hbottom 2,
    Nat.pow_le_pow_left hraw 3,Nat.mul_le_mul_left ((bits+2)^2) hone]

end RationalBits
end AFT.BinaryArithmetic

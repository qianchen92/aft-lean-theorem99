import AFT.BinaryEuclid
import AFT.RationalHeight

/-! Canonical rational data stored as Boolean lists. Proof fields are erased;
semantic reduced height controls the actual operand representation length. -/
namespace AFT.BinaryArithmetic

def signedValue (negative : Bool) (digits : List Bool) : ℤ :=
  if negative then -(value digits : ℤ) else (value digits : ℤ)

@[simp] theorem signedValue_natAbs (negative : Bool) (digits : List Bool) :
    (signedValue negative digits).natAbs=value digits := by
  cases negative <;> simp [signedValue]

structure RationalBits where
  negative : Bool
  numerator : List Bool
  denominator : List Bool
  numerator_normal : numerator.length=(value numerator).size
  denominator_normal : denominator.length=(value denominator).size
  denominator_positive : 0 < value denominator
  coprime : (value numerator).Coprime (value denominator)

namespace RationalBits

def decode (input : RationalBits) : ℚ :=
  Rat.mk' (signedValue input.negative input.numerator) (value input.denominator)
    input.denominator_positive.ne' (by simpa only [signedValue_natAbs] using input.coprime)

theorem decode_num (input : RationalBits) :
    input.decode.num=signedValue input.negative input.numerator := rfl

theorem decode_den (input : RationalBits) : input.decode.den=value input.denominator := rfl

theorem decode_fraction (input : RationalBits) :
    input.decode=(signedValue input.negative input.numerator : ℚ)/(value input.denominator : ℚ) := by
  rw [← Rat.num_div_den input.decode]
  rfl

theorem lengths_of_height (input : RationalBits) (bits : ℕ)
    (hh : AFT.RationalNumerics.HeightBound input.decode bits) :
    input.numerator.length ≤ bits+1 ∧ input.denominator.length ≤ bits+1 := by
  have hs := hh.binary_size
  simpa only [decode, signedValue_natAbs,← input.numerator_normal,← input.denominator_normal] using hs

end RationalBits

structure RationalResult where
  data : RationalBits
  work : ℕ

/-- Actual Euclid, two actual binary divisions, then high-zero trimming. -/
def reduce (negative : Bool) (num den : List Bool) (hden : 0 < value den) : RationalResult :=
  let common := gcd num den
  let top := divide num common.digits
  let bottom := divide den common.digits
  let nt := normalize top.quotient
  let nd := normalize bottom.quotient
  have hc : 0 < value common.digits := by
    simpa only [common,gcd_value] using Nat.gcd_pos_of_pos_right (value num) hden
  have ht : value nt.digits=value num/Nat.gcd (value num) (value den) := by
    simpa only [nt,normalize_value,top,common,gcd_value] using (divide_value num common.digits hc).1
  have hd : value nd.digits=value den/Nat.gcd (value num) (value den) := by
    simpa only [nd,normalize_value,bottom,common,gcd_value] using (divide_value den common.digits hc).1
  ⟨{negative := negative,numerator := nt.digits,denominator := nd.digits
    numerator_normal := by dsimp only [nt];rw [normalize_length,normalize_value]
    denominator_normal := by dsimp only [nd];rw [normalize_length,normalize_value]
    denominator_positive := by rw [hd];exact Nat.div_gcd_pos_of_pos_right _ hden
    coprime := by rw [ht,hd];exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hden)},
    common.work+top.work+bottom.work+nt.work+nd.work+8⟩

theorem reduce_numerator (negative : Bool) (num den : List Bool) (hden : 0 < value den) :
    value (reduce negative num den hden).data.numerator=value num/Nat.gcd (value num) (value den) := by
  have hc : 0 < value (gcd num den).digits := by rw [gcd_value];exact Nat.gcd_pos_of_pos_right _ hden
  simp only [reduce,normalize_value,(divide_value num (gcd num den).digits hc).1,gcd_value]

theorem reduce_denominator (negative : Bool) (num den : List Bool) (hden : 0 < value den) :
    value (reduce negative num den hden).data.denominator=value den/Nat.gcd (value num) (value den) := by
  have hc : 0 < value (gcd num den).digits := by rw [gcd_value];exact Nat.gcd_pos_of_pos_right _ hden
  simp only [reduce,normalize_value,(divide_value den (gcd num den).digits hc).1,gcd_value]

theorem reduce_value (negative : Bool) (num den : List Bool) (hden : 0 < value den) :
    (reduce negative num den hden).data.decode=(signedValue negative num : ℚ)/(value den : ℚ) := by
  rw [RationalBits.decode_fraction]
  have hneg : (reduce negative num den hden).data.negative=negative := rfl
  simp only [signedValue,hneg]
  rw [reduce_numerator,reduce_denominator]
  have hc : (Nat.gcd (value num) (value den) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right _ hden).ne'
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,Int.cast_neg,Int.cast_natCast]
  all_goals rw [Nat.cast_div (Nat.gcd_dvd_left ..),Nat.cast_div (Nat.gcd_dvd_right ..)]
  all_goals first | exact hc | field_simp [hc]

theorem reduce_work (negative : Bool) (num den : List Bool) (hden : 0 < value den) :
    (reduce negative num den hden).work ≤ 2000*(num.length+den.length+1)^3 := by
  have hg := gcd_resources num den
  have ht := divide_work num (gcd num den).digits
  have hd := divide_work den (gcd num den).digits
  have htl := divide_quotient_length num (gcd num den).digits
  have hdl := divide_quotient_length den (gcd num den).digits
  simp only [reduce,normalize_work]
  rw [htl,hdl]
  have htop : num.length+(gcd num den).digits.length+1 ≤ 2*(num.length+den.length+1) := by omega
  have hbot : den.length+(gcd num den).digits.length+1 ≤ 2*(num.length+den.length+1) := by omega
  have hone : 1 ≤ num.length+den.length+1 := by omega
  nlinarith [hg.2,Nat.pow_le_pow_left htop 2,Nat.pow_le_pow_left hbot 2,
    Nat.mul_le_mul_left ((num.length+den.length+1)^2) hone]

end AFT.BinaryArithmetic

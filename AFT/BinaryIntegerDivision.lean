import AFT.BinaryIntegerData

/-! Euclidean residues and exact quotients of signed binary integers. No
loop depends on the decoded magnitude. -/
namespace AFT.BinaryArithmetic.IntegerBits
open AFT.RationalRejectionProgram

def residue (input : IntegerBits) (modulus : List Bool) : Result :=
  let division := divide input.digits modulus
  let rest := normalize division.remainder
  if input.negative && !rest.digits.isEmpty then
    let reflected := BinaryArithmetic.subtract false modulus rest.digits
    ⟨reflected.digits,division.work+rest.work+reflected.work+4⟩
  else ⟨rest.digits,division.work+rest.work+4⟩

theorem residue_value (input : IntegerBits) (modulus : List Bool) (hq : 0 < value modulus) :
    (value (residue input modulus).digits : ℤ)=input.decode%(value modulus : ℤ) := by
  have hr := (divide_value input.digits modulus hq).2
  have hn : value (normalize (divide input.digits modulus).remainder).digits=value input.digits%value modulus := by
    rw [normalize_value,hr]
  have hz : (normalize (divide input.digits modulus).remainder).digits.isEmpty=true ↔
      value input.digits%value modulus=0 := by
    rw [List.isEmpty_iff,normalize_nil_iff,hr]
  have hlt := Nat.mod_lt (value input.digits) hq
  cases hs : input.negative with
  | false =>
      simp only [residue,hs,Bool.false_and,Bool.false_eq_true,ite_false,hn,decode,signedValue,Int.natCast_emod]
  | true =>
      by_cases hd : value modulus ∣ value input.digits
      · have he : (normalize (divide input.digits modulus).remainder).digits.isEmpty=true := hz.mpr (Nat.mod_eq_zero_of_dvd hd)
        have hdi : (value modulus : ℤ) ∣ (value input.digits : ℤ) := by exact_mod_cast hd
        simp only [residue,hs,he,Bool.not_true,Bool.and_false,Bool.false_eq_true,ite_false,hn,
          Nat.mod_eq_zero_of_dvd hd,Nat.cast_zero,decode,signedValue,ite_true,Int.neg_emod,hdi,ite_true]
      · have he : (normalize (divide input.digits modulus).remainder).digits.isEmpty=false := by
          apply Bool.eq_false_iff.mpr
          intro hh
          exact hd (Nat.dvd_of_mod_eq_zero (hz.mp hh))
        have hdi : ¬(value modulus : ℤ) ∣ (value input.digits : ℤ) := by exact_mod_cast hd
        have hsub := BinaryArithmetic.subtract_value modulus
          (normalize (divide input.digits modulus).remainder).digits (by rw [hn];omega)
        simp only [residue,hs,he,Bool.not_false,Bool.true_and,ite_true,hsub,hn,
          decode,signedValue,Int.neg_emod,hdi,ite_false,Int.natAbs_natCast,←Int.natCast_emod]
        exact Int.natCast_sub (by omega)

theorem residue_length (input : IntegerBits) (modulus : List Bool) :
    (residue input modulus).digits.length ≤ input.digits.length+modulus.length := by
  have hd := divide_remainder_length input.digits modulus
  have hn := normalize_length_le (divide input.digits modulus).remainder
  unfold residue
  dsimp only
  split
  · simp only [BinaryArithmetic.subtract_length];omega
  · exact hn.trans hd

theorem residue_work (input : IntegerBits) (modulus : List Bool) :
    (residue input modulus).work ≤ 60*(input.digits.length+modulus.length+1)^2+10 := by
  have hd := divide_work input.digits modulus
  have hl := divide_remainder_length input.digits modulus
  have hn := normalize_length_le (divide input.digits modulus).remainder
  have hp : 1 ≤ input.digits.length+modulus.length+1 := by omega
  unfold residue
  dsimp only
  split
  · simp only [normalize_work,BinaryArithmetic.subtract_work]
    have hm : max modulus.length (normalize (divide input.digits modulus).remainder).digits.length ≤
        input.digits.length+modulus.length+1 := by omega
    nlinarith [Nat.mul_le_mul_left (input.digits.length+modulus.length+1) hp]
  · simp only [normalize_work]
    nlinarith [Nat.mul_le_mul_left (input.digits.length+modulus.length+1) hp]

def exactQuotient (input : IntegerBits) (modulus : List Bool) : CountedValue IntegerBits :=
  let division := divide input.digits modulus
  ⟨⟨input.negative,division.quotient⟩,division.work+2⟩

theorem exactQuotient_value (input : IntegerBits) (modulus : List Bool) (hq : 0 < value modulus)
    (hdiv : (value modulus : ℤ) ∣ input.decode) :
    (exactQuotient input modulus).value.decode=input.decode/(value modulus : ℤ) := by
  have hv := (divide_value input.digits modulus hq).1
  cases hs : input.negative with
  | false => simp only [exactQuotient,decode,signedValue,hs,Bool.false_eq_true,ite_false,hv,Int.natCast_ediv]
  | true =>
      have hd : (value modulus : ℤ) ∣ (value input.digits : ℤ) := by
        simpa only [decode,signedValue,hs,ite_true,dvd_neg] using hdiv
      simp only [exactQuotient,decode,signedValue,hs,ite_true,hv,Int.natCast_ediv,Int.neg_ediv_of_dvd hd]

theorem exactQuotient_length (input : IntegerBits) (modulus : List Bool) :
    (exactQuotient input modulus).value.digits.length=input.digits.length := divide_quotient_length ..
theorem exactQuotient_work (input : IntegerBits) (modulus : List Bool) :
    (exactQuotient input modulus).work ≤ 20*(input.digits.length+modulus.length+1)^2+2 :=
  Nat.add_le_add_right (divide_work ..) 2

end AFT.BinaryArithmetic.IntegerBits

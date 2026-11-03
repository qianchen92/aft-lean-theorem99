import AFT.BinaryRationalOperations

/-! # Actual binary clipping and natural ceiling

The ceiling uses binary long division, high-zero trimming, and one ripple
increment when the remainder is nonzero. Tests inspect the stored sign or
list constructor, never the decoded rational value.
-/
namespace AFT.BinaryArithmetic
namespace RationalBits

def maxZero (input : RationalBits) : RationalResult :=
  if input.negative then ⟨zero,2⟩ else ⟨input,2⟩

theorem maxZero_value (input : RationalBits) : (maxZero input).data.decode=max input.decode 0 := by
  have hd : (0 : ℚ) < value input.denominator := by exact_mod_cast input.denominator_positive
  cases hs : input.negative with
  | false =>
      have hp : 0≤ input.decode := by rw [decode_fraction];simp only [signedValue,hs,ite_false,Bool.false_eq_true];positivity
      simp only [maxZero,hs,ite_false,Bool.false_eq_true,max_eq_left hp]
  | true =>
      have hn : input.decode≤ 0 := by rw [decode_fraction];simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast];exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
      simp only [maxZero,hs,ite_true,zero_value,max_eq_right hn]

theorem maxZero_work (input : RationalBits) : (maxZero input).work=2 := by
  unfold maxZero
  split <;> rfl

private theorem ceil_fraction (num den : ℕ) (hd : 0 < den) :
    ⌈(num : ℚ)/(den : ℚ)⌉₊=if num%den=0 then num/den else num/den+1 := by
  have hdq : (0 : ℚ)<den := by exact_mod_cast hd
  have hb : num/den*den+num%den=num := by nlinarith [Nat.div_add_mod num den]
  have hr := Nat.mod_lt num hd
  split <;> rename_i hz
  · have he : (num : ℚ)/(den : ℚ)=(num/den : ℕ) := by
      apply (div_eq_iff hdq.ne').mpr
      have hn : num=num/den*den := by omega
      exact_mod_cast hn
    rw [he,Nat.ceil_natCast]
  · apply (Nat.ceil_eq_iff (Nat.succ_ne_zero (num/den))).mpr
    constructor
    · apply (lt_div_iff₀ hdq).mpr
      have hn : num/den*den<num := by omega
      exact_mod_cast hn
    · apply (div_le_iff₀ hdq).mpr
      have hn : num≤ (num/den+1)*den := by nlinarith
      exact_mod_cast hn

/-- Both output and all arithmetic intermediates are Boolean lists. -/
def ceilNatural (input : RationalBits) : Result :=
  if input.negative then ⟨[],2⟩ else
    let division := divide input.numerator input.denominator
    let remainder := normalize division.remainder
    let rounded : Result := if remainder.digits.isEmpty then
        ⟨division.quotient,1⟩
      else
        let increment := BinaryArithmetic.add false division.quotient [true]
        ⟨increment.digits,increment.work+1⟩
    let normalized := normalize rounded.digits
    ⟨normalized.digits,division.work+remainder.work+rounded.work+normalized.work+4⟩

theorem ceilNatural_value (input : RationalBits) : value (ceilNatural input).digits=⌈input.decode⌉₊ := by
  cases hs : input.negative with
  | true =>
      have hn : input.decode≤ 0 := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
      simp only [ceilNatural,hs,ite_true,value,Nat.ceil_eq_zero.mpr hn]
  | false =>
      have hq := divide_value input.numerator input.denominator input.denominator_positive
      have he : (normalize (divide input.numerator input.denominator).remainder).digits=[] ↔
          value input.numerator%value input.denominator=0 := by rw [normalize_nil_iff,hq.2]
      rw [decode_fraction]
      simp only [signedValue,hs,ite_false,Bool.false_eq_true,Int.cast_natCast]
      rw [ceil_fraction _ _ input.denominator_positive]
      simp only [ceilNatural,hs,ite_false,Bool.false_eq_true,normalize_value]
      by_cases hz : value input.numerator%value input.denominator=0
      · simp only [he.mpr hz,List.isEmpty_nil,ite_true,hq.1,hz]
      · have hne : (normalize (divide input.numerator input.denominator).remainder).digits≠[] :=
          fun hh => hz (he.mp hh)
        have hb : (normalize (divide input.numerator input.denominator).remainder).digits.isEmpty=false := by
          simpa only [List.isEmpty_eq_false_iff] using hne
        simp only [hb,ite_false,Bool.false_eq_true,BinaryArithmetic.add_value,value,Bool.toNat_true,Bool.toNat_false,hq.1,hz,
          Nat.mul_zero,Nat.add_zero]

theorem ceilNatural_length (input : RationalBits) :
    (ceilNatural input).digits.length=⌈input.decode⌉₊.size := by
  rw [← ceilNatural_value]
  unfold ceilNatural
  split
  · rfl
  · dsimp only
    rw [normalize_length,normalize_value]

theorem ceilNatural_le_numerator (input : RationalBits) :
    ⌈input.decode⌉₊≤ value input.numerator := by
  apply Nat.ceil_le.mpr
  rw [decode_fraction]
  have hd : (1 : ℚ)≤ value input.denominator := by exact_mod_cast input.denominator_positive
  have hp : (0 : ℚ)≤ value input.numerator := by positivity
  cases hs : input.negative with
  | false =>
      simp only [signedValue,ite_false,Bool.false_eq_true,Int.cast_natCast]
      exact div_le_self hp hd
  | true =>
      simp only [signedValue,ite_true,Int.cast_neg,Int.cast_natCast]
      exact (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) (le_trans (by norm_num) hd)).trans hp

theorem ceilNatural_length_of_height (input : RationalBits) (bits : ℕ)
    (hh : AFT.RationalNumerics.HeightBound input.decode bits) :
    (ceilNatural input).digits.length≤ bits+1 := by
  rw [ceilNatural_length]
  have hc := Nat.size_le_size (ceilNatural_le_numerator input)
  have hn := (lengths_of_height input bits hh).1
  rw [← input.numerator_normal] at hc
  exact hc.trans hn

theorem ceilNatural_work (input : RationalBits) :
    (ceilNatural input).work≤ 100*(input.numerator.length+input.denominator.length+1)^2 := by
  have hw := divide_work input.numerator input.denominator
  have hq := divide_quotient_length input.numerator input.denominator
  have hr := divide_remainder_length input.numerator input.denominator
  have hl := add_length (divide input.numerator input.denominator).quotient [true] false
  have hm : max (divide input.numerator input.denominator).quotient.length 1≤ input.numerator.length+1 := by omega
  have hp : 1≤ input.numerator.length+input.denominator.length+1 := by omega
  unfold ceilNatural
  split
  · change 2≤ _
    have hh := Nat.one_le_pow 2 _ hp
    omega
  · dsimp only
    split
    · simp only [normalize_work,hq]
      nlinarith [Nat.mul_le_mul_left (input.numerator.length+input.denominator.length+1) hp]
    · simp only [normalize_work,BinaryArithmetic.add_work,List.length_cons,List.length_nil,Nat.zero_add]
      simp only [List.length_cons,List.length_nil,Nat.zero_add] at hl
      nlinarith [Nat.mul_le_mul_left (input.numerator.length+input.denominator.length+1) hp]

theorem ceilNatural_work_of_height (input : RationalBits) (bits : ℕ)
    (hh : AFT.RationalNumerics.HeightBound input.decode bits) :
    (ceilNatural input).work≤ 900*(bits+2)^2 := by
  obtain ⟨hn,hd⟩ := lengths_of_height input bits hh
  have hs : input.numerator.length+input.denominator.length+1≤ 3*(bits+2) := by omega
  have hw := ceilNatural_work input
  nlinarith [Nat.pow_le_pow_left hs 2]

end RationalBits
end AFT.BinaryArithmetic

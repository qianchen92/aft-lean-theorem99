import AFT.BinaryFiniteArithmetic
import AFT.BinaryRationalControl
import AFT.RationalAcceptanceCoin

/-! Binary floor and clipping, for executable dyadic probability tables. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def floorNatural (input : RationalBits) : Result :=
  if input.negative then ⟨[],2⟩ else
    let division := divide input.numerator input.denominator
    let result := normalize division.quotient
    ⟨result.digits,division.work+result.work+3⟩

theorem floorNatural_value (input : RationalBits) : value (floorNatural input).digits=⌊input.decode⌋₊ := by
  cases hs : input.negative with
  | true =>
      have hn : input.decode≤ 0 := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
      simp only [floorNatural,hs,ite_true,value,Nat.floor_of_nonpos hn]
  | false =>
      have hq := (divide_value input.numerator input.denominator input.denominator_positive).1
      rw [decode_fraction]
      simp only [signedValue,hs,ite_false,Bool.false_eq_true,Int.cast_natCast,Rat.natFloor_natCast_div_natCast,
        floorNatural,normalize_value,hq]

theorem floorNatural_length (input : RationalBits) :
    (floorNatural input).digits.length=⌊input.decode⌋₊.size := by
  rw [← floorNatural_value]
  unfold floorNatural
  split
  · rfl
  · dsimp only
    rw [normalize_length,normalize_value]

theorem floorNatural_le_numerator (input : RationalBits) : ⌊input.decode⌋₊≤ value input.numerator :=
  (Nat.floor_le_ceil input.decode).trans (ceilNatural_le_numerator input)

theorem floorNatural_length_of_height (input : RationalBits) (bits : ℕ)
    (hh : HeightBound input.decode bits) : (floorNatural input).digits.length≤ bits+1 := by
  rw [floorNatural_length]
  have hc := Nat.size_le_size (floorNatural_le_numerator input)
  rw [← input.numerator_normal] at hc
  exact hc.trans (lengths_of_height input bits hh).1

theorem floorNatural_work (input : RationalBits) (bits : ℕ) (hh : HeightBound input.decode bits) :
    (floorNatural input).work≤ 1000*(bits+2)^2 := by
  have hw := divide_work input.numerator input.denominator
  have hq := divide_quotient_length input.numerator input.denominator
  obtain ⟨hn,hd⟩ := lengths_of_height input bits hh
  have hs : input.numerator.length+input.denominator.length+1≤ 3*(bits+2) := by omega
  have hp : 1≤ (bits+2)^2 := Nat.one_le_pow _ _ (by omega)
  unfold floorNatural
  split
  · change 2≤ _
    omega
  · simp only [normalize_work,hq]
    nlinarith [Nat.pow_le_pow_left hs 2]

/-- Clipping tests the numerator against the denominator by borrow. -/
def clipUnit (input : RationalBits) : RationalResult :=
  if input.negative then ⟨zero,2⟩ else
    let comparison := subtract false input.numerator input.denominator
    ⟨if comparison.borrow then input else one,comparison.work+3⟩

theorem clipUnit_value (input : RationalBits) :
    (clipUnit input).data.decode=RationalAcceptanceCoin.clipped input.decode := by
  have hd : (0 : ℚ)<value input.denominator := by exact_mod_cast input.denominator_positive
  cases hs : input.negative with
  | true =>
      have hn : input.decode≤ 0 := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hd.le
      simp only [clipUnit,hs,ite_true,zero_value,RationalAcceptanceCoin.clipped,max_eq_right hn,
        min_eq_right (by norm_num : (0 : ℚ)≤ 1)]
  | false =>
      have he : input.decode=(value input.numerator : ℚ)/(value input.denominator : ℚ) := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_false,Bool.false_eq_true,Int.cast_natCast]
      have hn : 0≤ input.decode := by rw [he];positivity
      simp only [clipUnit,hs,ite_false,Bool.false_eq_true,RationalAcceptanceCoin.clipped,max_eq_left hn]
      split <;> rename_i hb
      · have hc := (subtract_borrow input.numerator input.denominator).mp hb
        have hh : input.decode<1 := by rw [he,div_lt_one hd];exact_mod_cast hc
        exact (min_eq_right hh.le).symm
      · have hc : value input.denominator≤ value input.numerator := by
          exact Nat.le_of_not_gt (fun hh => hb ((subtract_borrow input.numerator input.denominator).mpr hh))
        have hh : 1≤ input.decode := by rw [he,le_div_iff₀ hd];simpa only [one_mul] using (show (value input.denominator : ℚ)≤value input.numerator by exact_mod_cast hc)
        rw [one_value,min_eq_left hh]

theorem clipUnit_height (input : RationalBits) (bits : ℕ) (hh : HeightBound input.decode bits) :
    HeightBound (clipUnit input).data.decode bits := by
  unfold clipUnit
  split
  · simpa only [zero_value] using HeightBound.zero.mono (Nat.zero_le bits)
  · dsimp only
    split
    · exact hh
    · simpa only [one_value] using HeightBound.one.mono (Nat.zero_le bits)

theorem clipUnit_work (input : RationalBits) (bits : ℕ) (hh : HeightBound input.decode bits) :
    (clipUnit input).work≤ 10*(bits+1)+5 := by
  obtain ⟨hn,hd⟩ := lengths_of_height input bits hh
  unfold clipUnit
  split
  · change 2≤ _
    omega
  · simp only [subtract_work]
    omega

end AFT.BinaryArithmetic.RationalBits

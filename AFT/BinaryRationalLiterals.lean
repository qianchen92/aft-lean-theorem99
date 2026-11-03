import AFT.BinaryRationalIntegers

/-! Finite stored literals and explicit copying. `exists_code` is a semantic
encoding theorem; it is not a runtime rational-to-bits oracle. Programs store
its finite Boolean literals before execution. -/
namespace AFT.BinaryArithmetic

def copy : List Bool → Result
  | [] => ⟨[],1⟩
  | bit::tail => let previous := copy tail;⟨bit::previous.digits,previous.work+2⟩

theorem copy_digits (digits : List Bool) : (copy digits).digits=digits := by
  induction digits with
  | nil => rfl
  | cons bit tail ih => simp only [copy,ih]

theorem copy_work (digits : List Bool) : (copy digits).work=2*digits.length+1 := by
  induction digits with
  | nil => rfl
  | cons bit tail ih => simp only [copy,ih,List.length_cons];omega

theorem bits_value (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec with
  | zero => simp [value]
  | bit b n ih =>
    by_cases hn : n=0
    · subst n
      cases b <;> simp [Nat.bit_val,value]
    · rw [Nat.bits_append_bit n b (fun hh => False.elim (hn hh))]
      simp only [value,ih,Nat.bit_val]
      omega

namespace RationalBits

def copy (input : RationalBits) : RationalResult :=
  let num := BinaryArithmetic.copy input.numerator
  let den := BinaryArithmetic.copy input.denominator
  ⟨{negative := input.negative,numerator := num.digits,denominator := den.digits
    numerator_normal := by simpa only [num,copy_digits] using input.numerator_normal
    denominator_normal := by simpa only [den,copy_digits] using input.denominator_normal
    denominator_positive := by simpa only [den,copy_digits] using input.denominator_positive
    coprime := by simpa only [num,den,copy_digits] using input.coprime},num.work+den.work+2⟩

theorem copy_value (input : RationalBits) : (copy input).data.decode=input.decode := by
  rw [decode_fraction,decode_fraction]
  simp only [copy,copy_digits]

theorem copy_work (input : RationalBits) (bits : ℕ)
    (hh : AFT.RationalNumerics.HeightBound input.decode bits) :
    (copy input).work ≤ 4*bits+8 := by
  obtain ⟨hn,hd⟩ := input.lengths_of_height bits hh
  simp only [copy,BinaryArithmetic.copy_work]
  omega

/-- Existence of a finite literal encoding, used when constructing a fixed
program. The result is stored data, not an invocation of a real oracle. -/
theorem exists_code (q : ℚ) : ∃ code : RationalBits,code.decode=q := by
  let negative := decide (q.num < 0)
  have hsign : signedValue negative q.num.natAbs.bits=q.num := by
    simp only [signedValue,bits_value,negative]
    by_cases hn : q.num < 0
    · simp [hn,abs_of_neg hn]
    · simp [hn,abs_of_nonneg (by omega : 0 ≤ q.num)]
  let code : RationalBits :=
    ⟨negative,q.num.natAbs.bits,q.den.bits,
      by rw [bits_value,Nat.size_eq_bits_len],
      by rw [bits_value,Nat.size_eq_bits_len],
      by simpa only [bits_value] using q.den_pos,
      by simpa only [bits_value] using q.reduced⟩
  refine ⟨code,?_⟩
  rw [decode_fraction]
  change (signedValue negative q.num.natAbs.bits : ℚ)/(value q.den.bits : ℚ)=q
  rw [hsign,bits_value,Rat.num_div_den]

end RationalBits
end AFT.BinaryArithmetic

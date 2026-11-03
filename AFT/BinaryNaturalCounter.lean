import AFT.BinaryNormalization

/-! # Converting bounded loop counters into binary digits

The input is a unary loop counter. Each successor calls the actual ripple
adder; no whole-integer arithmetic is used in the digit result. The bound
is deliberately polynomial in the counter's value. In finite Gaussian
series the counters themselves are polynomially bounded in the dimension.
This is not a claim of polynomial time in the bit length of an arbitrary
unbounded integer.
-/
namespace AFT.BinaryArithmetic

def counterDigits : ℕ → Result
  | 0 => ⟨[],2⟩
  | count+1 =>
      let previous := counterDigits count
      let next := add false previous.digits [true]
      ⟨next.digits,previous.work+next.work+3⟩

theorem counterDigits_value (count : ℕ) : value (counterDigits count).digits=count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [counterDigits,add_value,value,Bool.toNat_true,Bool.toNat_false,ih]

theorem counterDigits_length (count : ℕ) : (counterDigits count).digits.length≤ 2*count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hh := add_length (counterDigits count).digits [true] false
      simp only [counterDigits,List.length_cons,List.length_nil] at hh ⊢
      omega

theorem counterDigits_work (count : ℕ) : (counterDigits count).work≤ 40*(count+1)^2 := by
  induction count with
  | zero => norm_num [counterDigits]
  | succ count ih =>
      have hl := counterDigits_length count
      have hm : max (counterDigits count).digits.length 1≤ 2*count+1 := by omega
      simp only [counterDigits,add_work,List.length_cons,List.length_nil,Nat.zero_add]
      nlinarith

/-- The normalized result is ready for canonical rational construction. -/
def canonicalCounter (count : ℕ) : Result :=
  let raw := counterDigits count
  let normalized := normalize raw.digits
  ⟨normalized.digits,raw.work+normalized.work+2⟩

theorem canonicalCounter_value (count : ℕ) : value (canonicalCounter count).digits=count := by
  simp only [canonicalCounter,normalize_value,counterDigits_value]

theorem canonicalCounter_length (count : ℕ) : (canonicalCounter count).digits.length=count.size := by
  simp only [canonicalCounter,normalize_length,counterDigits_value]

theorem canonicalCounter_work (count : ℕ) : (canonicalCounter count).work≤ 50*(count+1)^2 := by
  have hw := counterDigits_work count
  have hl := counterDigits_length count
  simp only [canonicalCounter,normalize_work]
  nlinarith

end AFT.BinaryArithmetic

import AFT.BinarySubtraction

/-! Linear-time removal of high zero digits. -/
namespace AFT.BinaryArithmetic

def normalize : List Bool → Result
  | [] => ⟨[],2⟩
  | bit::tail =>
    let previous := normalize tail
    match previous.digits with
    | [] => ⟨if bit then [true] else [],previous.work+4⟩
    | next::rest => ⟨bit::next::rest,previous.work+4⟩

theorem normalize_value (digits : List Bool) : value (normalize digits).digits=value digits := by
  induction digits with
  | nil => rfl
  | cons bit tail ih =>
    simp only [normalize]
    split <;> rename_i he
    · rw [he] at ih
      cases bit <;> simp only [ite_false,ite_true,Bool.false_eq_true,value,Bool.toNat_false,Bool.toNat_true] at * <;> omega
    · simp only [value]
      rw [← ih,he]
      rfl

theorem normalize_length (digits : List Bool) :
    (normalize digits).digits.length=(value digits).size := by
  induction digits with
  | nil => simp [normalize,value]
  | cons bit tail ih =>
    have hv := normalize_value tail
    simp only [normalize]
    split <;> rename_i he
    · rw [he] at ih hv
      simp only [value] at hv
      cases bit <;> simp [value,hv.symm]
    · have ht : value tail ≠ 0 := by
        intro ht
        rw [ht,Nat.size_zero,he] at ih
        simp at ih
      have hn : Nat.bit bit (value tail) ≠ 0 := by
        rw [Nat.bit_val]
        have hbit : bit.toNat ≤ 1 := by cases bit <;> decide
        omega
      have hs := Nat.size_bit hn
      rw [he] at ih
      simp only [List.length_cons] at ih
      simp only [List.length_cons,value]
      rw [Nat.bit_val] at hs
      have hvEq : bit.toNat+2*value tail=2*value tail+bit.toNat := by omega
      rw [hvEq,hs]
      omega

theorem normalize_length_le (digits : List Bool) : (normalize digits).digits.length ≤ digits.length := by
  rw [normalize_length]
  exact Nat.size_le.mpr (value_lt digits)

theorem normalize_nil_iff (digits : List Bool) : (normalize digits).digits=[] ↔ value digits=0 := by
  rw [← List.length_eq_zero_iff,normalize_length]
  exact Nat.size_eq_zero

theorem normalize_work (digits : List Bool) : (normalize digits).work=4*digits.length+2 := by
  induction digits with
  | nil => rfl
  | cons bit tail ih =>
    simp only [normalize]
    split <;> simp only [List.length_cons] <;> omega

end AFT.BinaryArithmetic

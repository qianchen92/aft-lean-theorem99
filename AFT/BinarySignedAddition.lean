import AFT.BinaryRationalData

/-! Signed-magnitude addition, implemented by the Boolean ripple algorithms. -/
namespace AFT.BinaryArithmetic

structure SignedResult where
  negative : Bool
  digits : List Bool
  work : ℕ

def signedAdd (firstSign secondSign : Bool) (first second : List Bool) : SignedResult :=
  if firstSign==secondSign then
    let sum := add false first second
    ⟨firstSign,sum.digits,sum.work+3⟩
  else
    let diff := subtract false first second
    if diff.borrow then
      let reverse := subtract false second first
      ⟨secondSign,reverse.digits,diff.work+reverse.work+4⟩
    else ⟨firstSign,diff.digits,diff.work+4⟩

theorem signedAdd_value (firstSign secondSign : Bool) (first second : List Bool) :
    signedValue (signedAdd firstSign secondSign first second).negative
      (signedAdd firstSign secondSign first second).digits =
      signedValue firstSign first+signedValue secondSign second := by
  have hadd := add_value first second false
  simp only [Bool.toNat_false,Nat.add_zero] at hadd
  by_cases he : firstSign=secondSign
  · subst secondSign
    simp only [signedAdd,beq_self_eq_true,ite_true,signedValue,hadd]
    cases firstSign <;> simp
    omega
  · have hbeq : (firstSign==secondSign)=false := by simpa using he
    simp only [signedAdd,hbeq,Bool.false_eq_true,ite_false]
    cases hb : (subtract false first second).borrow with
    | true =>
      have hlt := (subtract_borrow first second).mp hb
      have hv := subtract_value second first hlt.le
      simp only [ite_true,signedValue,hv]
      cases firstSign <;> cases secondSign <;> simp_all <;> omega
    | false =>
      have hle : value second ≤ value first := by
        have hh := (subtract_borrow first second)
        simp only [hb,Bool.false_eq_true,false_iff] at hh
        omega
      have hv := subtract_value first second hle
      simp only [Bool.false_eq_true,ite_false,signedValue,hv]
      cases firstSign <;> cases secondSign <;> simp_all <;> omega

theorem signedAdd_length (firstSign secondSign : Bool) (first second : List Bool) :
    (signedAdd firstSign secondSign first second).digits.length ≤ max first.length second.length+1 := by
  simp only [signedAdd]
  split
  · exact add_length ..
  · split <;> simp only [subtract_length];all_goals omega

theorem signedAdd_work (firstSign secondSign : Bool) (first second : List Bool) :
    (signedAdd firstSign secondSign first second).work ≤ 20*max first.length second.length+8 := by
  simp only [signedAdd]
  split
  · simp only [add_work];omega
  · split <;> simp only [subtract_work] <;> omega

end AFT.BinaryArithmetic

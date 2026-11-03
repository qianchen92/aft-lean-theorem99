import AFT.BinaryLoopControl
import AFT.BinaryDivision

/-! Long division of polynomially bounded unary addresses. Conversion to
and from digit lists is executed and charged; division itself is binary. -/
namespace AFT.BinaryArithmetic

structure CounterDivisionResult where
  quotient : ℕ
  remainder : ℕ
  work : ℕ

def divideCounter (numerator denominator : ℕ) : CounterDivisionResult :=
  let first := canonicalCounter numerator
  let second := canonicalCounter denominator
  let division := divide first.digits second.digits
  let quotient := readCounter division.quotient
  let remainder := readCounter division.remainder
  ⟨quotient.count,remainder.count,first.work+second.work+division.work+quotient.work+remainder.work+5⟩

theorem divideCounter_value (numerator denominator : ℕ) (hd : 0<denominator) :
    (divideCounter numerator denominator).quotient=numerator/denominator ∧
      (divideCounter numerator denominator).remainder=numerator%denominator := by
  have h := divide_value (canonicalCounter numerator).digits (canonicalCounter denominator).digits
    (by simpa only [canonicalCounter_value] using hd)
  simpa only [divideCounter,readCounter_value,canonicalCounter_value] using h

theorem divideCounter_work (numerator denominator : ℕ) (hd : 0<denominator) :
    (divideCounter numerator denominator).work ≤ 500*(numerator+denominator+2)^2 := by
  have hn := canonicalCounter_work numerator
  have hm := canonicalCounter_work denominator
  have hdv := divide_work (canonicalCounter numerator).digits (canonicalCounter denominator).digits
  have hq := readCounter_work (divide (canonicalCounter numerator).digits (canonicalCounter denominator).digits).quotient
  have hr := readCounter_work (divide (canonicalCounter numerator).digits (canonicalCounter denominator).digits).remainder
  have hv := divide_value (canonicalCounter numerator).digits (canonicalCounter denominator).digits
    (by simpa only [canonicalCounter_value] using hd)
  have hql := divide_quotient_length (canonicalCounter numerator).digits (canonicalCounter denominator).digits
  have hrl := divide_remainder_length (canonicalCounter numerator).digits (canonicalCounter denominator).digits
  have hs (n : ℕ) : n.size≤n := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))
  simp only [canonicalCounter_value,canonicalCounter_length] at hv hql hrl hdv
  rw [hv.1,hql] at hq
  rw [hv.2] at hr
  have hqbound := Nat.div_le_self numerator denominator
  have hrbound := Nat.mod_lt numerator hd
  have hdivbound : 20*(numerator.size+denominator.size+1)^2≤20*(numerator+denominator+1)^2 := by
    gcongr <;> exact hs _
  have hnsize := hs numerator
  have hdsize := hs denominator
  have hrl' : (divide (canonicalCounter numerator).digits (canonicalCounter denominator).digits).remainder.length≤numerator+denominator := by omega
  simp only [divideCounter]
  nlinarith

/-- Truncated subtraction is a genuine simultaneous unary traversal. -/
def differenceCounter : ℕ → ℕ → UnaryCounterResult
  | first,0 => ⟨first,1⟩
  | 0,_+1 => ⟨0,1⟩
  | first+1,second+1 =>
      let previous := differenceCounter first second
      ⟨previous.count,previous.work+2⟩

theorem differenceCounter_value (first second : ℕ) :
    (differenceCounter first second).count=first-second := by
  induction second generalizing first with
  | zero => simp [differenceCounter]
  | succ second ih =>
      cases first with
      | zero => simp [differenceCounter]
      | succ first => simpa only [differenceCounter,Nat.succ_sub_succ_eq_sub] using ih first

theorem differenceCounter_work (first second : ℕ) :
    (differenceCounter first second).work ≤ 2*first+1 := by
  induction second generalizing first with
  | zero => simp only [differenceCounter];omega
  | succ second ih =>
      cases first with
      | zero => simp [differenceCounter]
      | succ first => simp only [differenceCounter];have h := ih first;omega

end AFT.BinaryArithmetic

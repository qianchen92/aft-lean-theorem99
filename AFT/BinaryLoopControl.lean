import AFT.BinaryNaturalCounter

/-! # Explicit unary loop control for polynomially bounded counters

The represented counter is a unary natural. Reading a binary counter costs
linear time in its numerical value and list length. This overhead is used
only when the surrounding finite-series proof bounds the counter itself
by a polynomial in the dimension.
-/
namespace AFT.BinaryArithmetic

structure UnaryCounterResult where
  count : ℕ
  work : ℕ

/-- Unary doubling uses two successor constructors per iteration. -/
def doubleCounter : ℕ → UnaryCounterResult
  | 0 => ⟨0,1⟩
  | count+1 =>
      let previous := doubleCounter count
      ⟨previous.count.succ.succ,previous.work+3⟩

theorem doubleCounter_value (count : ℕ) : (doubleCounter count).count=2*count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [doubleCounter,ih];omega

theorem doubleCounter_work (count : ℕ) : (doubleCounter count).work=3*count+1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [doubleCounter,ih];omega

/-- The execution uses only list cases, unary doubling and successor. -/
def readCounter : List Bool → UnaryCounterResult
  | [] => ⟨0,2⟩
  | bit::tail =>
      let previous := readCounter tail
      let doubled := doubleCounter previous.count
      ⟨if bit then doubled.count.succ else doubled.count,previous.work+doubled.work+3⟩

theorem readCounter_value (digits : List Bool) : (readCounter digits).count=value digits := by
  induction digits with
  | nil => rfl
  | cons bit tail ih =>
      cases bit <;> simp only [readCounter,doubleCounter_value,ih,value,Bool.false_eq_true,ite_false,
        ite_true,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem readCounter_work (digits : List Bool) :
    (readCounter digits).work≤ 6*value digits+4*digits.length+2 := by
  induction digits with
  | nil => simp only [readCounter,value,List.length_nil];omega
  | cons bit tail ih =>
      simp only [readCounter,doubleCounter_work,readCounter_value,value,List.length_cons]
      omega

/-- Unary addition traverses its first input; it is never charged as a
constant-time operation on an unbounded whole integer. -/
def addCounter : ℕ → ℕ → UnaryCounterResult
  | 0,second => ⟨second,1⟩
  | first+1,second =>
      let previous := addCounter first second
      ⟨previous.count.succ,previous.work+2⟩

theorem addCounter_value (first second : ℕ) : (addCounter first second).count=first+second := by
  induction first with
  | zero => simp only [addCounter,Nat.zero_add]
  | succ first ih => simp only [addCounter,ih];omega

theorem addCounter_work (first second : ℕ) : (addCounter first second).work=2*first+1 := by
  induction first with
  | zero => rfl
  | succ first ih => simp only [addCounter,ih];omega

/-- Unary multiplication is repeated actual unary addition. -/
def multiplyCounter : ℕ → ℕ → UnaryCounterResult
  | 0,_ => ⟨0,1⟩
  | first+1,second =>
      let previous := multiplyCounter first second
      let next := addCounter second previous.count
      ⟨next.count,previous.work+next.work+2⟩

theorem multiplyCounter_value (first second : ℕ) : (multiplyCounter first second).count=first*second := by
  induction first with
  | zero => simp only [multiplyCounter,Nat.zero_mul]
  | succ first ih => simp only [multiplyCounter,addCounter_value,ih];ring

theorem multiplyCounter_work (first second : ℕ) :
    (multiplyCounter first second).work=first*(2*second+3)+1 := by
  induction first with
  | zero => simp only [multiplyCounter,Nat.zero_mul,Nat.zero_add]
  | succ first ih => simp only [multiplyCounter,addCounter_work,ih];ring

end AFT.BinaryArithmetic

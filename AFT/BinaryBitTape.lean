import AFT.BinaryNormalization
import AFT.PermutationProgramCost

/-! Linear-time construction of powers of two and direct reading of a fair
bit tape into little-endian digits. There is no enumeration of its values. -/
namespace AFT.BinaryArithmetic

def powerTwoDigits : ℕ → Result
  | 0 => ⟨[true],2⟩
  | bits+1 => let previous := powerTwoDigits bits;⟨false::previous.digits,previous.work+2⟩

theorem powerTwoDigits_value (bits : ℕ) : value (powerTwoDigits bits).digits=2^bits := by
  induction bits with
  | zero => simp [powerTwoDigits,value]
  | succ bits ih => simp only [powerTwoDigits,value,Bool.toNat_false,Nat.zero_add,ih,pow_succ']

theorem powerTwoDigits_length (bits : ℕ) : (powerTwoDigits bits).digits.length=bits+1 := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [powerTwoDigits,List.length_cons,ih]

theorem powerTwoDigits_work (bits : ℕ) : (powerTwoDigits bits).work=2*bits+2 := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [powerTwoDigits,ih];omega

def digitBoolean (digit : Fin 2) : Bool := decide (digit.val=1)

theorem digitBoolean_value (digit : Fin 2) : (digitBoolean digit).toNat=digit.val := by
  fin_cases digit <;> rfl

/-- Each input bit is read exactly once in increasing position order. -/
def readBitTape : (bits : ℕ) → (Fin bits → Fin 2) → Result
  | 0,_ => ⟨[],2⟩
  | bits+1,word =>
      let previous := readBitTape bits (Fin.tail word)
      ⟨digitBoolean (word 0)::previous.digits,previous.work+3⟩

theorem readBitTape_value (bits : ℕ) (word : Fin bits → Fin 2) :
    value (readBitTape bits word).digits=(FiniteTicketSampler.bitTicket bits word).val := by
  rw [← PermutationProgram.bitValue_value]
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [readBitTape,value,digitBoolean_value,ih,PermutationProgram.bitValue]

theorem readBitTape_length (bits : ℕ) (word : Fin bits → Fin 2) :
    (readBitTape bits word).digits.length=bits := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [readBitTape,List.length_cons,ih]

theorem readBitTape_work (bits : ℕ) (word : Fin bits → Fin 2) : (readBitTape bits word).work=3*bits+2 := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [readBitTape,ih];omega

end AFT.BinaryArithmetic

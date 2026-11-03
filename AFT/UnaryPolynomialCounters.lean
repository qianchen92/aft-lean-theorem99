import AFT.BinaryChartMetadata

/-! # Explicit arithmetic on polynomially bounded unary counters

These routines are used only for metadata whose numerical magnitude is itself
polynomial in the dimension. Exponential ticket counts never use this encoding.
-/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

def powerCounter (base : ℕ) : ℕ → UnaryCounterResult
  | 0 => ⟨1,2⟩
  | exponent+1 =>
      let previous := powerCounter base exponent
      let next := multiplyCounter base previous.count
      ⟨next.count,previous.work+next.work+2⟩

theorem powerCounter_value (base exponent : ℕ) : (powerCounter base exponent).count=base^exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp only [powerCounter,multiplyCounter_value,ih,pow_succ];ring

def powerCounterWork (base exponent : ℕ) : ℕ := (exponent+1)*(6*(base+1)^(exponent+2)+4)

theorem powerCounter_work (base exponent : ℕ) :
    (powerCounter base exponent).work≤ powerCounterWork base exponent := by
  induction exponent with
  | zero => simp only [powerCounter,powerCounterWork];omega
  | succ exponent ih =>
      have hp : (base+1)^(exponent+2)≤(base+1)^(exponent+1+2) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hb : base≤(base+1)^(exponent+1+2) := by
        calc
          _ ≤ base+1 := by omega
          _ = (base+1)^1 := by simp
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      have hm : base*base^exponent≤(base+1)^(exponent+1+2) := by
        calc
          _ = base^(exponent+1) := by rw [pow_succ];ring
          _ ≤ (base+1)^(exponent+1) := Nat.pow_le_pow_left (by omega) _
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      have hi : (powerCounter base exponent).work≤(exponent+1)*(6*(base+1)^(exponent+1+2)+4) :=
        ih.trans (Nat.mul_le_mul_left _ (by omega))
      simp only [powerCounter,multiplyCounter_work,powerCounter_value,powerCounterWork]
      nlinarith

theorem powerCounterWork_mono {base larger : ℕ} (h : base≤larger) (exponent : ℕ) :
    powerCounterWork base exponent≤powerCounterWork larger exponent := by
  unfold powerCounterWork
  gcongr

def lessCounter : ℕ → ℕ → CountedValue Bool
  | _,0 => ⟨false,2⟩
  | 0,_+1 => ⟨true,2⟩
  | first+1,second+1 => let previous := lessCounter first second;⟨previous.value,previous.work+3⟩

theorem lessCounter_value (first second : ℕ) : (lessCounter first second).value=true ↔ first<second := by
  induction first generalizing second with
  | zero => cases second <;> simp [lessCounter]
  | succ first ih => cases second <;> simp [lessCounter,ih]

theorem lessCounter_work (first second : ℕ) : (lessCounter first second).work≤3*(first+second)+2 := by
  induction first generalizing second with
  | zero => cases second <;> simp only [lessCounter] <;> omega
  | succ first ih =>
      cases second with
      | zero => simp only [lessCounter];omega
      | succ second => have hh := ih second;simp only [lessCounter];omega

theorem lessCounter_work_right (first second : ℕ) : (lessCounter first second).work≤3*second+2 := by
  induction second generalizing first with
  | zero => simp only [lessCounter];omega
  | succ second ih =>
      cases first with
      | zero => simp only [lessCounter];omega
      | succ first => have hh := ih first;simp only [lessCounter];omega

theorem lessCounter_work_left (first second : ℕ) : (lessCounter first second).work≤3*first+2 := by
  induction first generalizing second with
  | zero => cases second <;> simp only [lessCounter] <;> omega
  | succ first ih =>
      cases second with
      | zero => simp only [lessCounter];omega
      | succ second => have hh := ih second;simp only [lessCounter];omega

def subtractCounter : ℕ → ℕ → UnaryCounterResult
  | first,0 => ⟨first,2⟩
  | 0,_+1 => ⟨0,2⟩
  | first+1,second+1 => let previous := subtractCounter first second;⟨previous.count,previous.work+2⟩

theorem subtractCounter_value (first second : ℕ) : (subtractCounter first second).count=first-second := by
  induction first generalizing second with
  | zero => cases second <;> simp [subtractCounter]
  | succ first ih => cases second <;> simp [subtractCounter,ih]

theorem subtractCounter_work_left (first second : ℕ) : (subtractCounter first second).work≤2*first+2 := by
  induction first generalizing second with
  | zero => cases second <;> simp only [subtractCounter] <;> omega
  | succ first ih =>
      cases second with
      | zero => simp only [subtractCounter];omega
      | succ second => have hh := ih second;simp only [subtractCounter];omega

end AFT.BinaryArithmetic

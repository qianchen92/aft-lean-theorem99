import AFT.BinaryRationalOperations
import AFT.BinaryRationalIntegers
import AFT.BinaryNaturalCounter
import AFT.RationalSeriesHeight

/-! Powers, factorials, and finite sums on actual canonical binary rationals. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
open scoped BigOperators

def one : RationalBits := ⟨false,[true],[true],by decide,by decide,by decide,by decide⟩
def minusOne : RationalBits := ⟨true,[true],[true],by decide,by decide,by decide,by decide⟩
def half : RationalBits := ⟨false,[true],[false,true],by decide,by decide,by decide,by decide⟩
def third : RationalBits := ⟨false,[true],[true,true],by decide,by decide,by decide,by decide⟩
def four : RationalBits := ⟨false,[false,false,true],[true],by decide,by decide,by decide,by decide⟩

@[simp] theorem one_value : one.decode=1 := by decide
@[simp] theorem minusOne_value : minusOne.decode=(-1 : ℚ) := by decide
@[simp] theorem half_value : half.decode=(1/2 : ℚ) := by rw [decode_fraction];norm_num [half,signedValue,value]
@[simp] theorem third_value : third.decode=(1/3 : ℚ) := by rw [decode_fraction];norm_num [third,signedValue,value]
@[simp] theorem four_value : four.decode=(4 : ℚ) := by decide

theorem primitiveWorkBound_mono {first second : ℕ} (h : first ≤ second) :
    primitiveWorkBound first ≤ primitiveWorkBound second := by
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

def quotient (first second : RationalBits) : RationalResult :=
  let inv := inverse second
  let result := multiply first inv.data
  ⟨result.data,inv.work+result.work+2⟩

theorem quotient_value (first second : RationalBits) :
    (quotient first second).data.decode=first.decode/second.decode := by
  simp only [quotient,multiply_value,inverse_value,div_eq_mul_inv]

theorem quotient_work (first second : RationalBits) (bits : ℕ)
    (hf : HeightBound first.decode bits) (hs : HeightBound second.decode bits) :
    (quotient first second).work ≤ 2*primitiveWorkBound bits+2 := by
  have hi := inverse_work second bits
  have hm := multiply_work first (inverse second).data bits hf (by rw [inverse_value];exact hs.inv)
  simp only [quotient]
  omega

/-- The natural here is a polynomially bounded unary loop counter. Its
rational value is constructed by the actual binary counter, not a cast. -/
def ofCounter (count : ℕ) : RationalResult :=
  let counter := canonicalCounter count
  let result := ofNat counter.digits
  ⟨result.data,counter.work+result.work+2⟩

theorem ofCounter_value (count : ℕ) : (ofCounter count).data.decode=(count : ℚ) := by
  simp only [ofCounter,ofNat_value,canonicalCounter_value]

theorem ofCounter_work (count : ℕ) : (ofCounter count).work ≤ 60*(count+1)^2 := by
  have hc := canonicalCounter_work count
  have hl : count.size ≤ count := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=count))
  simp only [ofCounter,ofNat_work,canonicalCounter_length]
  nlinarith

def power (input : RationalBits) : ℕ → RationalResult
  | 0 => ⟨one,2⟩
  | count+1 =>
    let previous := power input count
    let result := multiply previous.data input
    ⟨result.data,previous.work+result.work+2⟩

theorem power_value (input : RationalBits) (count : ℕ) : (power input count).data.decode=input.decode^count := by
  induction count with
  | zero => simp [power]
  | succ count ih => simp only [power,multiply_value,ih,pow_succ]

theorem power_work_le (input : RationalBits) (bits limit count : ℕ)
    (hinput : HeightBound input.decode bits) (hcount : count ≤ limit) :
    (power input count).work ≤ count*(primitiveWorkBound (bits*(limit+1))+2)+2 := by
  induction count with
  | zero => simp [power]
  | succ count ih =>
    have hp : HeightBound (power input count).data.decode (bits*(limit+1)) := by
      rw [power_value]
      exact (hinput.pow count).mono (Nat.mul_le_mul_left _ (by omega))
    have hx : HeightBound input.decode (bits*(limit+1)) := hinput.mono (by nlinarith)
    have hm := multiply_work (power input count).data input (bits*(limit+1)) hp hx
    have hh := ih (by omega)
    simp only [power]
    nlinarith

theorem power_work (input : RationalBits) (bits count : ℕ) (hinput : HeightBound input.decode bits) :
    (power input count).work ≤ count*(primitiveWorkBound (bits*(count+1))+2)+2 :=
  power_work_le input bits count count hinput le_rfl

def factorial : ℕ → RationalResult
  | 0 => ⟨one,2⟩
  | count+1 =>
    let previous := factorial count
    let coefficient := ofCounter (count+1)
    let result := multiply coefficient.data previous.data
    ⟨result.data,previous.work+coefficient.work+result.work+2⟩

theorem factorial_value (count : ℕ) : (factorial count).data.decode=(count.factorial : ℚ) := by
  induction count with
  | zero => simp [factorial]
  | succ count ih => simp only [factorial,multiply_value,ofCounter_value,ih,Nat.factorial_succ,Nat.cast_mul]

def factorialWorkStep (limit : ℕ) : ℕ := 60*(limit+2)^2+primitiveWorkBound ((limit+1)^2)+2

theorem factorial_work_le (count limit : ℕ) (hcount : count ≤ limit) :
    (factorial count).work ≤ count*factorialWorkStep limit+2 := by
  induction count with
  | zero => simp [factorial]
  | succ count ih =>
    have hn := ofCounter_work (count+1)
    have hn' : (ofCounter (count+1)).work ≤ 60*(limit+2)^2 :=
      hn.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    have hp : HeightBound (factorial count).data.decode ((limit+1)^2) := by
      rw [factorial_value]
      exact (factorial_height count).mono (by nlinarith)
    have hx : HeightBound (ofCounter (count+1)).data.decode ((limit+1)^2) := by
      rw [ofCounter_value]
      exact (HeightBound.nat_coarse (count+1)).mono (by nlinarith)
    have hm := multiply_work (ofCounter (count+1)).data (factorial count).data ((limit+1)^2) hx hp
    have hh := ih (by omega)
    simp only [factorial,factorialWorkStep] at *
    nlinarith

def sumRange (term : ℕ → RationalResult) : ℕ → RationalResult
  | 0 => ⟨zero,2⟩
  | count+1 =>
    let previous := sumRange term count
    let next := term count
    let result := add previous.data next.data
    ⟨result.data,previous.work+next.work+result.work+2⟩

theorem sumRange_value (term : ℕ → RationalResult) (count : ℕ) :
    (sumRange term count).data.decode=∑ index∈Finset.range count,(term index).data.decode := by
  induction count with
  | zero => simp [sumRange]
  | succ count ih => simp only [sumRange,add_value,ih,Finset.sum_range_succ]

theorem sumRange_work (term : ℕ → RationalResult) (bits termWork count : ℕ)
    (hbits : ∀ index<count,HeightBound (term index).data.decode bits)
    (hwork : ∀ index<count,(term index).work ≤ termWork) :
    (sumRange term count).work ≤ count*(termWork+primitiveWorkBound ((count+1)*(bits+1))+2)+2 := by
  have haux : ∀ length ≤ count,(sumRange term length).work ≤
      length*(termWork+primitiveWorkBound ((count+1)*(bits+1))+2)+2 := by
    intro length
    induction length with
    | zero => intro _;simp [sumRange]
    | succ length ih =>
      intro hl
      have hp : HeightBound (sumRange term length).data.decode ((count+1)*(bits+1)) := by
        rw [sumRange_value]
        have hh := HeightBound.sum (Finset.range length) (fun index => (term index).data.decode) bits
          (fun index hi => hbits index (by have := Finset.mem_range.mp hi;omega))
        simp only [Finset.card_range] at hh
        exact hh.mono (Nat.mul_le_mul_right _ (by omega))
      have hx := (hbits length (by omega)).mono (show bits ≤ (count+1)*(bits+1) by nlinarith)
      have hm := add_work (sumRange term length).data (term length).data ((count+1)*(bits+1)) hp hx
      have hw := hwork length (by omega)
      have hh := ih (by omega)
      simp only [sumRange]
      nlinarith
  exact haux count le_rfl

end AFT.BinaryArithmetic.RationalBits

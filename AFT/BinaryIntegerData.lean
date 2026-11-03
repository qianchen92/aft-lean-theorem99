import AFT.BinarySignedAddition
import AFT.BinaryProtectedPalette
import AFT.BinaryDataArrays

/-! Signed integer data and actual bit algorithms. The decoded integers are
used only in proofs; all running operands remain Boolean lists. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

structure IntegerBits where
  negative : Bool
  digits : List Bool

namespace IntegerBits

def decode (input : IntegerBits) : ℤ := signedValue input.negative input.digits

def zero : IntegerBits := ⟨false,[]⟩
@[simp] theorem zero_value : zero.decode=0 := rfl

def ofSigned (input : SignedResult) : IntegerBits := ⟨input.negative,input.digits⟩

def negate (input : IntegerBits) : CountedValue IntegerBits := ⟨⟨!input.negative,input.digits⟩,2⟩
@[simp] theorem negate_value (input : IntegerBits) : (negate input).value.decode= -input.decode := signedValue_not ..
@[simp] theorem negate_length (input : IntegerBits) : (negate input).value.digits.length=input.digits.length := rfl
@[simp] theorem negate_work (input : IntegerBits) : (negate input).work=2 := rfl

def add (first second : IntegerBits) : CountedValue IntegerBits :=
  let result := signedAdd first.negative second.negative first.digits second.digits
  ⟨ofSigned result,result.work+1⟩
@[simp] theorem add_value (first second : IntegerBits) : (add first second).value.decode=first.decode+second.decode :=
  signedAdd_value ..
theorem add_length (first second : IntegerBits) :
    (add first second).value.digits.length ≤ max first.digits.length second.digits.length+1 := signedAdd_length ..
theorem add_work (first second : IntegerBits) :
    (add first second).work ≤ 20*max first.digits.length second.digits.length+9 :=
  Nat.add_le_add_right (signedAdd_work ..) 1

def subtract (first second : IntegerBits) : CountedValue IntegerBits :=
  let negative := negate second
  let result := add first negative.value
  ⟨result.value,negative.work+result.work+2⟩
@[simp] theorem subtract_value (first second : IntegerBits) :
    (subtract first second).value.decode=first.decode-second.decode := by
  simp only [subtract,add_value,negate_value,sub_eq_add_neg]
theorem subtract_length (first second : IntegerBits) :
    (subtract first second).value.digits.length ≤ max first.digits.length second.digits.length+1 := add_length ..
theorem subtract_work (first second : IntegerBits) :
    (subtract first second).work ≤ 20*max first.digits.length second.digits.length+13 := by
  have hh := add_work first (negate second).value
  simp only [subtract,negate_work,negate_length] at *
  omega

def multiply (first second : IntegerBits) : CountedValue IntegerBits :=
  let product := BinaryArithmetic.multiply first.digits second.digits
  ⟨⟨first.negative ^^ second.negative,product.digits⟩,product.work+2⟩
@[simp] theorem multiply_value (first second : IntegerBits) :
    (multiply first second).value.decode=first.decode*second.decode := by
  simp only [multiply,decode,signedValue,BinaryArithmetic.multiply_value]
  cases first.negative <;> cases second.negative <;> simp
theorem multiply_length (first second : IntegerBits) :
    (multiply first second).value.digits.length ≤ 2*first.digits.length+second.digits.length :=
  BinaryArithmetic.multiply_length ..
theorem multiply_work (first second : IntegerBits) :
    (multiply first second).work ≤ 20*(first.digits.length+second.digits.length+1)^2+2 := by
  have hh := BinaryArithmetic.multiply_work first.digits second.digits
  exact Nat.add_le_add_right hh 2

def sumFin : (count : ℕ) → (Fin count → CountedValue IntegerBits) → CountedValue IntegerBits
  | 0,_ => ⟨zero,2⟩
  | count+1,term =>
      let previous := sumFin count (fun index => term index.castSucc)
      let next := term (Fin.last count)
      let result := add previous.value next.value
      ⟨result.value,previous.work+next.work+result.work+2⟩

theorem sumFin_value (count : ℕ) (term : Fin count → CountedValue IntegerBits) :
    (sumFin count term).value.decode=∑ index,(term index).value.decode := by
  induction count with
  | zero => simp [sumFin]
  | succ count ih => simp only [sumFin,add_value,ih,Fin.sum_univ_castSucc]

theorem sumFin_length (count bits : ℕ) (term : Fin count → CountedValue IntegerBits)
    (h : ∀ index,(term index).value.digits.length ≤ bits) :
    (sumFin count term).value.digits.length ≤ count+bits := by
  induction count with
  | zero => simp [sumFin,zero]
  | succ count ih =>
      have hp := ih (fun index => term index.castSucc) (fun index => h index.castSucc)
      have hn := h (Fin.last count)
      exact (add_length _ _).trans (by omega)

theorem sumFin_work_limit (count limit bits queryWork : ℕ) (hc : count ≤ limit)
    (term : Fin count → CountedValue IntegerBits)
    (hb : ∀ index,(term index).value.digits.length ≤ bits)
    (hw : ∀ index,(term index).work ≤ queryWork) :
    (sumFin count term).work ≤ count*(queryWork+20*(limit+bits)+11)+2 := by
  induction count with
  | zero => simp [sumFin]
  | succ count ih =>
      have hp := ih (by omega) (fun index => term index.castSucc) (fun index => hb index.castSucc) (fun index => hw index.castSucc)
      have hl := sumFin_length count bits (fun index => term index.castSucc) (fun index => hb index.castSucc)
      have hn := hb (Fin.last count)
      have hnext := hw (Fin.last count)
      have ha := add_work (sumFin count (fun index => term index.castSucc)).value (term (Fin.last count)).value
      have hm : max (sumFin count (fun index => term index.castSucc)).value.digits.length
          (term (Fin.last count)).value.digits.length ≤ limit+bits := by omega
      simp only [sumFin]
      nlinarith

theorem sumFin_work (count bits queryWork : ℕ) (term : Fin count → CountedValue IntegerBits)
    (hb : ∀ index,(term index).value.digits.length ≤ bits) (hw : ∀ index,(term index).work ≤ queryWork) :
    (sumFin count term).work ≤ count*(queryWork+20*(count+bits)+11)+2 :=
  sumFin_work_limit count count bits queryWork le_rfl term hb hw

end IntegerBits
end AFT.BinaryArithmetic

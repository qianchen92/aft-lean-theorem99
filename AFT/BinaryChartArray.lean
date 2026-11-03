import AFT.BinaryFiniteArithmetic
import AFT.ScalarOperationalEvaluation

/-! Explicit sequential array access and finite arithmetic accumulation.
A lookup scans a list and charges the array-to-list copy; it is not a unit
cost random-access operation on an unbounded index. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.RationalNumerics
open scoped BigOperators

structure ReadResult (α : Type*) where
  data : Option α
  work : ℕ

def readList {α : Type*} : List α → ℕ → ReadResult α
  | [],_ => ⟨none,1⟩
  | head::_,0 => ⟨some head,2⟩
  | _::tail,index+1 => let result := readList tail index;⟨result.data,result.work+2⟩

theorem readList_value {α : Type*} (items : List α) (index : ℕ) :
    (readList items index).data=items[index]? := by
  induction items generalizing index with
  | nil => simp [readList]
  | cons head tail ih => cases index <;> simp [readList,ih]

theorem readList_work {α : Type*} (items : List α) (index : ℕ) :
    (readList items index).work ≤ 2*items.length+1 := by
  induction items generalizing index with
  | nil => simp [readList]
  | cons head tail ih =>
    cases index with
    | zero => simp only [readList,List.length_cons];omega
    | succ index => have hh := ih index;simp only [readList,List.length_cons];omega

def readVector {α : Type*} {count : ℕ} (fallback : α) (items : Vector α count) (index : Fin count) : CountedValue α :=
  let result := readList items.toList index.val
  ⟨result.data.getD fallback,result.work+count+2⟩

theorem readVector_value {α : Type*} {count : ℕ} (fallback : α) (items : Vector α count) (index : Fin count) :
    (readVector fallback items index).value=items.get index := by
  simp only [readVector,readList_value]
  rw [List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some,Vector.getElem_toList]
  rfl

theorem readVector_work {α : Type*} {count : ℕ} (fallback : α) (items : Vector α count) (index : Fin count) :
    (readVector fallback items index).work ≤ 3*count+3 := by
  have hh := readList_work items.toList index.val
  simp only [Vector.length_toList] at hh
  simp only [readVector]
  omega

namespace RationalBits

def sumFin : (count : ℕ) → (Fin count → RationalResult) → RationalResult
  | 0,_ => ⟨zero,2⟩
  | count+1,term =>
    let previous := sumFin count (fun index => term index.castSucc)
    let next := term (Fin.last count)
    let result := add previous.data next.data
    ⟨result.data,previous.work+next.work+result.work+2⟩

theorem sumFin_value (count : ℕ) (term : Fin count → RationalResult) :
    (sumFin count term).data.decode=∑ index,(term index).data.decode := by
  induction count with
  | zero => simp [sumFin]
  | succ count ih => simp only [sumFin,add_value,ih,Fin.sum_univ_castSucc]

theorem sumFin_height (count bits : ℕ) (term : Fin count → RationalResult)
    (h : ∀ index,HeightBound (term index).data.decode bits) :
    HeightBound (sumFin count term).data.decode (count*(bits+1)) := by
  rw [sumFin_value]
  simpa only [Finset.card_univ,Fintype.card_fin] using HeightBound.sum Finset.univ
    (fun index => (term index).data.decode) bits (fun index _ => h index)

theorem sumFin_work (count bits termWork : ℕ) (term : Fin count → RationalResult)
    (hh : ∀ index,HeightBound (term index).data.decode bits)
    (hw : ∀ index,(term index).work ≤ termWork) :
    (sumFin count term).work ≤ count*(termWork+primitiveWorkBound ((count+1)*(bits+1))+2)+2 := by
  induction count with
  | zero => simp [sumFin]
  | succ count ih =>
    have hp := sumFin_height count bits (fun index => term index.castSucc) (fun index => hh index.castSucc)
    have hx := hh (Fin.last count)
    have hm := add_work (sumFin count (fun index => term index.castSucc)).data (term (Fin.last count)).data
      ((count+1+1)*(bits+1)) (hp.mono (Nat.mul_le_mul_right _ (by omega)))
      (hx.mono (by nlinarith))
    have hv := hw (Fin.last count)
    have hi := ih (fun index => term index.castSucc) (fun index => hh index.castSucc) (fun index => hw index.castSucc)
    have hmono := primitiveWorkBound_mono (Nat.mul_le_mul_right (bits+1) (show count+1 ≤ count+1+1 by omega))
    simp only [sumFin]
    nlinarith

structure ArrayResult (count : ℕ) where
  data : Vector RationalBits count
  work : ℕ

def buildArray (count : ℕ) (term : Fin count → RationalResult) : ArrayResult count :=
  let computed := Vector.ofFn term
  ⟨computed.map (fun result => result.data),(∑ index,(computed.get index).work)+2*count+2⟩

theorem buildArray_get (count : ℕ) (term : Fin count → RationalResult) (index : Fin count) :
    (buildArray count term).data.get index=(term index).data := by
  simp [buildArray]

theorem buildArray_work (count budget : ℕ) (term : Fin count → RationalResult)
    (h : ∀ index,(term index).work ≤ budget) :
    (buildArray count term).work ≤ count*(budget+2)+2 := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun index _ => h index)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  simp only [buildArray,Vector.get_ofFn]
  nlinarith

end RationalBits
end AFT.BinaryArithmetic

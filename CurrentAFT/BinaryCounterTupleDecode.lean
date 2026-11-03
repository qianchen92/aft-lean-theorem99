import AFT.BinaryCounterDivision
import CurrentAFT.BinaryTupleSum
import CurrentAFT.WeightCoordinateDecode

/-! Fixed-degree radix decoding with actual binary long division and buffer reads. -/
namespace CurrentAFT.BinaryCounterTupleDecode
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def append {Value : Type*} {count : ℕ} (leading : Vector Value count) (last : Value) : CountedValue (Vector Value (count+1)) :=
  let entries := Vector.ofFn (fun index : Fin (count+1) =>
    Fin.lastCases (motive := fun _ => CountedValue Value) ⟨last,1⟩ (fun index => readVector last leading index) index)
  ⟨entries.map (fun entry => entry.value),(∑ index, (entries.get index).work)+2*(count+1)+2⟩

theorem append_get {Value : Type*} {count : ℕ} (leading : Vector Value count) (last : Value) (index : Fin (count+1)) :
    (append leading last).value.get index=Fin.lastCases last leading.get index := by
  refine Fin.lastCases ?_ (fun index => ?_) index <;> simp [append,readVector_value]

theorem append_work {Value : Type*} {count : ℕ} (leading : Vector Value count) (last : Value) :
    (append leading last).work ≤ (count+1)*(3*count+5)+2 := by
  have hh (index : Fin (count+1)) :
      (Fin.lastCases (motive := fun _ => CountedValue Value) ⟨last,1⟩ (fun index => readVector last leading index) index).work≤3*count+3 := by
    refine Fin.lastCases ?_ (fun index => ?_) index
    · simp only [Fin.lastCases_last]; omega
    · simpa only [Fin.lastCases_castSucc] using readVector_work last leading index
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun index _ => hh index)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  simp only [append,Vector.get_ofFn]
  nlinarith

def current (base : ℕ) (hb : 0<base) : (count : ℕ) → ℕ → CountedValue (Vector (Fin base) count)
  | 0,_ => ⟨#v[],1⟩
  | count+1,code =>
    let divided := divideCounter code base
    let previous := current base hb count divided.quotient
    let last : Fin base := ⟨divided.remainder, by rw [(divideCounter_value code base hb).2]; exact Nat.mod_lt _ hb⟩
    let result := append previous.value last
    ⟨result.value,divided.work+previous.work+result.work+3⟩

theorem current_get (base : ℕ) (hb : 0<base) (count code : ℕ) (index : Fin count) :
    (current base hb count code).value.get index=WeightCoordinates.tupleDecode base hb count code index := by
  induction count generalizing code with
  | zero => exact Fin.elim0 index
  | succ count ih =>
    simp only [current,append_get]
    refine Fin.lastCases ?_ (fun index => ?_) index
    · simp only [Fin.lastCases_last,WeightCoordinates.tupleDecode]
      apply Fin.ext
      exact (divideCounter_value code base hb).2
    · simp only [Fin.lastCases_castSucc,WeightCoordinates.tupleDecode,ih,(divideCounter_value code base hb).1]

def workBound (base capacity limit count : ℕ) : ℕ :=
  (count+1)*(500*(capacity+base+2)^2+(limit+1)*(3*limit+5)+5)

theorem current_work (base : ℕ) (hb : 0<base) (count code capacity limit : ℕ) (hc : code≤capacity) (hl : count≤limit) :
    (current base hb count code).work ≤ workBound base capacity limit count := by
  induction count generalizing code with
  | zero => simp only [current,workBound]; omega
  | succ count ih =>
    have hq : (divideCounter code base).quotient≤capacity := by
      rw [(divideCounter_value code base hb).1]
      exact (Nat.div_le_self code base).trans hc
    have hp := ih (divideCounter code base).quotient hq (by omega)
    have hd := (divideCounter_work code base hb).trans
      (show 500*(code+base+2)^2≤500*(capacity+base+2)^2 by gcongr)
    have ha := append_work (current base hb count (divideCounter code base).quotient).value
      (⟨(divideCounter code base).remainder,by rw [(divideCounter_value code base hb).2]; exact Nat.mod_lt _ hb⟩:Fin base)
    have hal : (count+1)*(3*count+5)+2 ≤ (limit+1)*(3*limit+5)+2 := by gcongr <;> omega
    have ha := ha.trans hal
    change _+_+_+3 ≤ _
    unfold workBound at hp ⊢
    nlinarith

end CurrentAFT.BinaryCounterTupleDecode

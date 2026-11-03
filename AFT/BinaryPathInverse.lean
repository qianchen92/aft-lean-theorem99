import AFT.BinaryIntegerDivision
import AFT.IntegerCoordinateProgram

/-! Integral path inversion on stored signed bit arrays. Each recursive
stage materializes its tail once and performs only actual bit additions. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

private def pathTailEntry {count : ℕ} (load : Vector IntegerBits (count+2)) (first : IntegerBits)
    (index : Fin (count+1)) : CountedValue IntegerBits :=
  let next := readVector IntegerBits.zero load index.succ
  let shifted := if index.val=0 then IntegerBits.add next.value first else ⟨next.value,1⟩
  ⟨shifted.value,next.work+shifted.work+3⟩

def binaryPathTail {count : ℕ} (load : Vector IntegerBits (count+2)) (first : IntegerBits) :
    CountedValue (Vector IntegerBits (count+1)) := storeData (count+1) (pathTailEntry load first)

theorem binaryPathTail_value {count : ℕ} (load : Vector IntegerBits (count+2)) (first : IntegerBits)
    (index : Fin (count+1)) :
    ((binaryPathTail load first).value.get index).decode=(load.get index.succ).decode+
      if index=0 then first.decode else 0 := by
  simp only [binaryPathTail,storeData_get,pathTailEntry,readVector_value]
  by_cases hi : index=0
  · subst index;simp [IntegerBits.add_value]
  · have hi' : index.val ≠ 0 := fun hh => hi (Fin.ext hh)
    simp [hi,hi']

theorem binaryPathTail_length {count bits : ℕ} (load : Vector IntegerBits (count+2)) (first : IntegerBits)
    (hl : ∀ index,(load.get index).digits.length ≤ bits) (hf : first.digits.length ≤ bits)
    (index : Fin (count+1)) : ((binaryPathTail load first).value.get index).digits.length ≤ bits+1 := by
  simp only [binaryPathTail,storeData_get,pathTailEntry,readVector_value]
  split
  · exact (IntegerBits.add_length _ _).trans (by have hh:=hl index.succ;omega)
  · exact (hl index.succ).trans (by omega)

theorem binaryPathTail_work {count bits : ℕ} (load : Vector IntegerBits (count+2)) (first : IntegerBits)
    (hl : ∀ index,(load.get index).digits.length ≤ bits) (hf : first.digits.length ≤ bits) :
    (binaryPathTail load first).work ≤ (count+1)*(3*(count+2)+20*bits+17)+2 := by
  apply storeData_work
  intro index
  have hr := readVector_work IntegerBits.zero load index.succ
  have hn : (readVector IntegerBits.zero load index.succ).value.digits.length ≤ bits := by rw [readVector_value];exact hl index.succ
  have ha := IntegerBits.add_work (readVector IntegerBits.zero load index.succ).value first
  have hm : max (readVector IntegerBits.zero load index.succ).value.digits.length first.digits.length ≤ bits := by omega
  simp only [pathTailEntry]
  split <;> (try dsimp only) <;> omega

def binaryPathInverse : (count : ℕ) → Vector IntegerBits (count+1) → CountedValue (Vector IntegerBits count)
  | 0,_ => ⟨#v[],2⟩
  | count+1,load =>
      let first := readVector IntegerBits.zero load 0
      let tail := binaryPathTail load first.value
      let remaining := binaryPathInverse count tail.value
      let result := storeData (count+1) (fun index => Fin.cases ⟨first.value,1⟩
        (fun rest => readVector IntegerBits.zero remaining.value rest) index)
      ⟨result.value,first.work+tail.work+remaining.work+result.work+4⟩

theorem binaryPathInverse_value (count : ℕ) (load : Vector IntegerBits (count+1)) (index : Fin count) :
    ((binaryPathInverse count load).value.get index).decode=
      (AFT.pathInverseProgram count (load.map IntegerBits.decode)).value.get index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      have ht : (binaryPathTail load (load.get 0)).value.map IntegerBits.decode=
          Vector.ofFn (fun slot : Fin (count+1) => (load.map IntegerBits.decode).get slot.succ+
            if slot=0 then (load.map IntegerBits.decode).get 0 else 0) := by
        apply Vector.ext
        intro slot hs
        change ((binaryPathTail load (load.get 0)).value.map IntegerBits.decode).get ⟨slot,hs⟩=
          (Vector.ofFn (fun slot : Fin (count+1) => (load.map IntegerBits.decode).get slot.succ+
            if slot=0 then (load.map IntegerBits.decode).get 0 else 0)).get ⟨slot,hs⟩
        simp only [Vector.get_map,Vector.get_ofFn,binaryPathTail_value]
      refine Fin.cases ?_ (fun rest => ?_) index
      · simp only [binaryPathInverse,storeData_get,Fin.cases_zero,readVector_value,
          AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_zero,Vector.get_map]
      · simp only [binaryPathInverse,storeData_get,Fin.cases_succ,readVector_value,
          AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_succ]
        rw [ih,ht]

theorem binaryPathInverse_length (count bits : ℕ) (load : Vector IntegerBits (count+1))
    (hl : ∀ index,(load.get index).digits.length ≤ bits) (index : Fin count) :
    ((binaryPathInverse count load).value.get index).digits.length ≤ count+bits := by
  induction count generalizing bits with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      have hfirst : (readVector IntegerBits.zero load 0).value.digits.length ≤ bits := by rw [readVector_value];exact hl 0
      have htail := binaryPathTail_length load (readVector IntegerBits.zero load 0).value hl hfirst
      simp only [readVector_value] at htail
      refine Fin.cases ?_ (fun rest => ?_) index
      · simp only [binaryPathInverse,storeData_get,Fin.cases_zero,readVector_value]
        exact (hl 0).trans (by omega)
      · simp only [binaryPathInverse,storeData_get,Fin.cases_succ,readVector_value]
        exact by
          have hh := ih (bits+1) (binaryPathTail load (load.get 0)).value htail rest
          simpa only [Nat.add_assoc,Nat.add_comm 1 bits] using hh

def binaryPathInverseWork (count bits : ℕ) : ℕ := count*(100*(count+bits+3)^2)+2

theorem binaryPathInverse_work (count bits : ℕ) (load : Vector IntegerBits (count+1))
    (hl : ∀ index,(load.get index).digits.length ≤ bits) :
    (binaryPathInverse count load).work ≤ binaryPathInverseWork count bits := by
  induction count generalizing bits with
  | zero => simp [binaryPathInverse,binaryPathInverseWork]
  | succ count ih =>
      let first := readVector IntegerBits.zero load 0
      let tail := binaryPathTail load first.value
      let remaining := binaryPathInverse count tail.value
      have hfirst : first.value.digits.length ≤ bits := by dsimp only [first];rw [readVector_value];exact hl 0
      have htail := binaryPathTail_length load first.value hl hfirst
      have hp := ih (bits+1) tail.value htail
      have wf := readVector_work IntegerBits.zero load 0
      have wt := binaryPathTail_work load first.value hl hfirst
      have wr := storeData_work (count+1) (3*count+3)
        (fun index : Fin (count+1) => Fin.cases (⟨first.value,1⟩ : CountedValue IntegerBits)
          (fun rest => readVector IntegerBits.zero remaining.value rest) index)
        (fun index => Fin.cases (by simp only [Fin.cases_zero];omega) (fun rest => readVector_work _ _ rest) index)
      change first.work+tail.work+remaining.work+_+4 ≤ _
      change first.work ≤ _ at wf
      change tail.work ≤ _ at wt
      change remaining.work ≤ _ at hp
      unfold binaryPathInverseWork at hp ⊢
      nlinarith

end AFT.BinaryArithmetic

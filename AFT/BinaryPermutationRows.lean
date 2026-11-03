import AFT.BinaryPermutationChoice
import AFT.BinaryDataArrays
import AFT.BinaryChartMetadata

/-! Stored permutation rows from the actual insertion sampler. Each old image
is explicitly read, compared, and written; no permutation oracle is used. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

def insertionImage {count : ℕ} (picked : Fin (count+1)) (image : Fin count) : CountedValue (Fin (count+1)) :=
  let equal := equalCounter image.val.succ picked.val
  ⟨if equal.value then 0 else image.succ,equal.work+2⟩

theorem insertionImage_value {count : ℕ} (picked : Fin (count+1)) (image : Fin count) :
    (insertionImage picked image).value=Equiv.swap 0 picked image.succ := by
  have he : (equalCounter image.val.succ picked.val).value=true ↔ image.succ=picked := by
    rw [equalCounter_value]
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  simp only [insertionImage,he,Equiv.swap_apply_def,Fin.succ_ne_zero,↓reduceIte]

theorem insertionImage_work {count : ℕ} (picked : Fin (count+1)) (image : Fin count) :
    (insertionImage picked image).work ≤ 6*count+10 := by
  have h := equalCounter_work image.val.succ picked.val
  have hi := image.isLt
  have hp := picked.isLt
  simp only [Nat.succ_eq_add_one] at h
  simp only [insertionImage,Nat.succ_eq_add_one]
  omega

def binaryPermutationRows (bits : ℕ) : (count : ℕ) → (Fin count → Fin bits → Fin 2) →
    CountedValue (Vector (Fin count) count)
  | 0,_ => ⟨Vector.ofFn Fin.elim0,2⟩
  | count+1,word =>
      let previous := binaryPermutationRows bits count (Fin.tail word)
      let selected := binaryPermutationChoice count bits (word 0)
      let result := storeData (count+1) (fun index => Fin.cases ⟨selected.value,1⟩ (fun old =>
        let read := readVector old previous.value old
        let image := insertionImage selected.value read.value
        ⟨image.value,read.work+image.work+2⟩) index)
      ⟨result.value,previous.work+selected.work+result.work+3⟩

theorem binaryPermutationRows_value (bits count : ℕ) (word : Fin count → Fin bits → Fin 2)
    (index : Fin count) :
    (binaryPermutationRows bits count word).value.get index=PermutationProgram.rows bits count word index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun old => ?_) index
      · simp only [binaryPermutationRows,storeData_get,Fin.cases_zero,PermutationProgram.rows,
          Equiv.Perm.decomposeFin_symm_apply_zero,binaryPermutationChoice_value]
      · simp only [binaryPermutationRows,storeData_get,Fin.cases_succ,insertionImage_value,
          readVector_value,ih,PermutationProgram.rows,Equiv.Perm.decomposeFin_symm_apply_succ,
          binaryPermutationChoice_value]

def binaryPermutationRowsWork (count bits : ℕ) : ℕ :=
  count*(binaryPermutationChoiceWork count bits+(count+1)*(9*count+17)+5)+2

theorem binaryPermutationRows_work_limit (bits count limit : ℕ) (hc : count ≤ limit)
    (word : Fin count → Fin bits → Fin 2) :
    (binaryPermutationRows bits count word).work ≤
      count*(binaryPermutationChoiceWork limit bits+(limit+1)*(9*limit+17)+5)+2 := by
  induction count with
  | zero => simp only [binaryPermutationRows,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ count ih =>
    let previous := binaryPermutationRows bits count (Fin.tail word)
    let selected := binaryPermutationChoice count bits (word 0)
    have hp := ih (by omega) (Fin.tail word)
    change previous.work ≤ _ at hp
    have hs := (binaryPermutationChoice_work count bits (word 0)).trans
      (binaryPermutationChoiceWork_mono (by omega : count ≤ limit) le_rfl)
    change selected.work ≤ _ at hs
    let entry : Fin (count+1) → CountedValue (Fin (count+1)) := fun index => Fin.cases (⟨selected.value,1⟩ : CountedValue (Fin (count+1))) (fun old =>
      let read := readVector old previous.value old
      let image := insertionImage selected.value read.value
      ⟨image.value,read.work+image.work+2⟩) index
    have he (index : Fin (count+1)) : (entry index).work ≤ 9*count+15 := by
      refine Fin.cases ?_ (fun old => ?_) index
      · simp only [entry,Fin.cases_zero];omega
      · have hr := readVector_work old previous.value old
        have hi := insertionImage_work selected.value (readVector old previous.value old).value
        simp only [entry,Fin.cases_succ]
        omega
    have hb := storeData_work (count+1) (9*count+15) entry he
    have hm : (count+1)*(9*count+17) ≤ (limit+1)*(9*limit+17) := by gcongr <;> omega
    change previous.work+selected.work+(storeData (count+1) entry).work+3 ≤ _
    nlinarith

theorem binaryPermutationRows_work (bits count : ℕ) (word : Fin count → Fin bits → Fin 2) :
    (binaryPermutationRows bits count word).work ≤ binaryPermutationRowsWork count bits :=
  binaryPermutationRows_work_limit bits count count le_rfl word

end AFT.BinaryArithmetic

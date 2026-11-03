import AFT.BinaryPermutationPolynomials

/-! Stored tape regrouping and actual public permutation draws. Index products
and sums are evaluated by counter programs before each sequential tape read. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

def binaryTapeCell {count bits : ℕ} (tape : Vector (Fin 2) (count*bits))
    (row : Fin count) (column : Fin bits) : CountedValue (Fin 2) :=
  let block := multiplyCounter bits row.val
  let offset := addCounter column.val block.count
  have hindex : offset.count < count*bits := by
    rw [addCounter_value,multiplyCounter_value]
    exact (finProdFinEquiv (row,column)).isLt
  let result := readVector 0 tape ⟨offset.count,hindex⟩
  ⟨result.value,block.work+offset.work+result.work+3⟩

theorem binaryTapeCell_value {count bits : ℕ} (tape : Vector (Fin 2) (count*bits))
    (row : Fin count) (column : Fin bits) :
    (binaryTapeCell tape row column).value=tape.get (finProdFinEquiv (row,column)) := by
  simp only [binaryTapeCell,readVector_value,addCounter_value,multiplyCounter_value]
  rfl

def binaryTapeCellWork (count bits : ℕ) : ℕ := bits*(2*count+3)+2*bits+3*(count*bits)+8

theorem binaryTapeCell_work {count bits : ℕ} (tape : Vector (Fin 2) (count*bits))
    (row : Fin count) (column : Fin bits) :
    (binaryTapeCell tape row column).work ≤ binaryTapeCellWork count bits := by
  have hr := readVector_work (0 : Fin 2) tape
    (⟨column.val+bits*row.val,(finProdFinEquiv (row,column)).isLt⟩ : Fin (count*bits))
  have hm : bits*(2*row.val+3) ≤ bits*(2*count+3) := by gcongr;exact Nat.le_of_lt row.isLt
  have hc := column.isLt
  simp only [binaryTapeCell,multiplyCounter_work,addCounter_work,multiplyCounter_value,addCounter_value]
  change bits*(2*row.val+3)+1+(2*column.val+1)+
    (readVector 0 tape ⟨column.val+bits*row.val,_⟩).work+3 ≤ _
  unfold binaryTapeCellWork
  omega

def binaryGroupTape (count bits : ℕ) (tape : Vector (Fin 2) (count*bits)) :
    CountedValue (Vector (Vector (Fin 2) bits) count) :=
  storeData count (fun row => storeData bits (binaryTapeCell tape row))

theorem binaryGroupTape_value (count bits : ℕ) (tape : Vector (Fin 2) (count*bits))
    (row : Fin count) (column : Fin bits) :
    ((binaryGroupTape count bits tape).value.get row).get column=
      AFT.FiniteConditionProgram.groupBits count bits tape.get row column := by
  simp only [binaryGroupTape,storeData_get,binaryTapeCell_value,AFT.FiniteConditionProgram.groupBits,Equiv.coe_fn_mk]

def binaryGroupTapeWork (count bits : ℕ) : ℕ := count*(bits*(binaryTapeCellWork count bits+2)+4)+2

theorem binaryGroupTape_work (count bits : ℕ) (tape : Vector (Fin 2) (count*bits)) :
    (binaryGroupTape count bits tape).work ≤ binaryGroupTapeWork count bits := by
  exact storeData_work count (bits*(binaryTapeCellWork count bits+2)+2) _
    (fun row => storeData_work bits (binaryTapeCellWork count bits) _ (binaryTapeCell_work tape row))

def binaryPermutationFromTape (count bits : ℕ) (tape : Vector (Fin 2) (count*bits)) :
    CountedValue (Vector (Fin count) count) :=
  let grouped := binaryGroupTape count bits tape
  let rows := binaryPermutationRows bits count (fun row => (grouped.value.get row).get)
  ⟨rows.value,grouped.work+rows.work+2⟩

theorem binaryPermutationFromTape_value (count bits : ℕ) (tape : Vector (Fin 2) (count*bits))
    (index : Fin count) :
    (binaryPermutationFromTape count bits tape).value.get index=
      AFT.PermutationProgram.draw count bits tape.get index := by
  simp only [binaryPermutationFromTape,binaryPermutationRows_value]
  have he : (fun row => ((binaryGroupTape count bits tape).value.get row).get)=
      AFT.FiniteConditionProgram.groupBits count bits tape.get := by
    funext row column
    exact binaryGroupTape_value count bits tape row column
  rw [he]
  rfl

def binaryPermutationFromTapeWork (count bits : ℕ) : ℕ :=
  binaryGroupTapeWork count bits+binaryPermutationRowsWork count bits+2

theorem binaryPermutationFromTape_work (count bits : ℕ) (tape : Vector (Fin 2) (count*bits)) :
    (binaryPermutationFromTape count bits tape).work ≤ binaryPermutationFromTapeWork count bits := by
  have hg := binaryGroupTape_work count bits tape
  have hr := binaryPermutationRows_work bits count (fun row => ((binaryGroupTape count bits tape).value.get row).get)
  exact Nat.add_le_add_right (Nat.add_le_add hg hr) 2

noncomputable def binaryPermutationFromTapePolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(bits*(bits*(2*count+3)+2*bits+3*(count*bits)+10)+4)+2+
    binaryPermutationRowsPolynomial count bits+2
@[simp] theorem binaryPermutationFromTapePolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (binaryPermutationFromTapePolynomial count bits).eval n=
      binaryPermutationFromTapeWork (count.eval n) (bits.eval n) := by
  simp [binaryPermutationFromTapePolynomial,binaryPermutationFromTapeWork,binaryGroupTapeWork,binaryTapeCellWork]

end AFT.BinaryArithmetic

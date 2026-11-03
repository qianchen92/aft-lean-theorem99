import AFT.BinaryRoundingInverse

/-! Materializing permuted matrix columns and the padded offset uses sequential
array reads and signed bit arithmetic, including every inner-product term. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 def readIntegerMatrix {size : ℕ} (matrix : Vector (Vector IntegerBits size) size)
     (column row : Fin size) : CountedValue IntegerBits :=
   let selected := readList matrix.toList column.val
   match selected.data with
   | none => ⟨IntegerBits.zero,selected.work+size+4⟩
   | some entry =>
       let result := readVector IntegerBits.zero entry row
       ⟨result.value,selected.work+result.work+size+4⟩

 theorem readIntegerMatrix_value {size : ℕ} (matrix : Vector (Vector IntegerBits size) size)
     (column row : Fin size) : (readIntegerMatrix matrix column row).value=(matrix.get column).get row := by
   simp only [readIntegerMatrix,readList_value]
   rw [List.getElem?_eq_getElem (by simp only [Vector.length_toList];exact column.isLt)]
   simp only [Vector.getElem_toList,readVector_value]
   rfl

 theorem readIntegerMatrix_work {size : ℕ} (matrix : Vector (Vector IntegerBits size) size)
     (column row : Fin size) : (readIntegerMatrix matrix column row).work≤6*size+8 := by
   have hs := readList_work matrix.toList column.val
   simp only [Vector.length_toList] at hs
   unfold readIntegerMatrix
   dsimp only
   split
   · dsimp only
     omega
   · rename_i entry he
     have hr := readVector_work IntegerBits.zero entry row
     dsimp only
     omega

 def binaryPermutedColumn (count : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (column : Fin (count+1)) :
     CountedValue (Vector IntegerBits (count+1)) :=
   storeData (count+1) (fun vertex =>
     let row := readVector 0 permutation vertex
     let result := readIntegerMatrix matrix column row.value
     ⟨result.value,row.work+result.work+2⟩)

 theorem binaryPermutedColumn_value (count : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (column vertex : Fin (count+1)) :
     (binaryPermutedColumn count matrix permutation column).value.get vertex=
       (matrix.get column).get (permutation.get vertex) := by
   simp only [binaryPermutedColumn,storeData_get,readIntegerMatrix_value,readVector_value]

 theorem binaryPermutedColumn_work (count : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (column : Fin (count+1)) :
     (binaryPermutedColumn count matrix permutation column).work≤(count+1)*(9*(count+1)+15)+2 := by
   apply storeData_work
   intro vertex
   have hp := readVector_work 0 permutation vertex
   have hm := readIntegerMatrix_work matrix column (readVector 0 permutation vertex).value
   dsimp only
   omega

 private def paddedProduct {size : ℕ} (matrix : Vector (Vector IntegerBits size) size)
     (padding : Vector IntegerBits size) (row column : Fin size) : CountedValue IntegerBits :=
   let weight := readVector IntegerBits.zero padding column
   let entry := readIntegerMatrix matrix column row
   let product := IntegerBits.multiply weight.value entry.value
   ⟨product.value,weight.work+entry.work+product.work+3⟩

 private theorem paddedProduct_value {size : ℕ} (matrix : Vector (Vector IntegerBits size) size)
     (padding : Vector IntegerBits size) (row column : Fin size) :
     (paddedProduct matrix padding row column).value.decode=
       (padding.get column).decode*((matrix.get column).get row).decode := by
   simp only [paddedProduct,IntegerBits.multiply_value,readVector_value,readIntegerMatrix_value]

 private theorem paddedProduct_length {size bits : ℕ} (matrix : Vector (Vector IntegerBits size) size)
     (padding : Vector IntegerBits size) (row column : Fin size)
     (hm : ∀ column row,((matrix.get column).get row).digits.length≤bits)
     (hp : ∀ column,(padding.get column).digits.length≤bits) :
     (paddedProduct matrix padding row column).value.digits.length≤3*bits := by
   have hh := IntegerBits.multiply_length (padding.get column) ((matrix.get column).get row)
   simp only [paddedProduct,readVector_value,readIntegerMatrix_value]
   have hm' := hm column row
   have hp' := hp column
   omega

 private theorem paddedProduct_work {size bits : ℕ} (matrix : Vector (Vector IntegerBits size) size)
     (padding : Vector IntegerBits size) (row column : Fin size)
     (hm : ∀ column row,((matrix.get column).get row).digits.length≤bits)
     (hp : ∀ column,(padding.get column).digits.length≤bits) :
     (paddedProduct matrix padding row column).work≤9*size+20*(2*bits+1)^2+16 := by
   have hr := readVector_work IntegerBits.zero padding column
   have he := readIntegerMatrix_work matrix column row
   have hx := IntegerBits.multiply_work (padding.get column) ((matrix.get column).get row)
   have hmx : (IntegerBits.multiply (padding.get column) ((matrix.get column).get row)).work≤20*(2*bits+1)^2+2 :=
     hx.trans (by
       have hp' := hp column
       have hm' := hm column row
       gcongr
       omega)
   simp only [paddedProduct,readVector_value,readIntegerMatrix_value]
   omega

 def binaryPaddedEntry (count : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (vertex : Fin (count+1)) : CountedValue IntegerBits :=
   let row := readVector 0 permutation vertex
   let original := readVector IntegerBits.zero initial row.value
   let total := IntegerBits.sumFin (count+1) (paddedProduct matrix padding row.value)
   let result := IntegerBits.add original.value total.value
   ⟨result.value,row.work+original.work+total.work+result.work+4⟩

 theorem binaryPaddedEntry_value (count : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (vertex : Fin (count+1)) :
     (binaryPaddedEntry count matrix initial padding permutation vertex).value.decode=
       (initial.get (permutation.get vertex)).decode+
         ∑ column,(padding.get column).decode*((matrix.get column).get (permutation.get vertex)).decode := by
   simp only [binaryPaddedEntry,IntegerBits.add_value,IntegerBits.sumFin_value,paddedProduct_value,readVector_value]

 theorem binaryPaddedEntry_length (count bits : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1))
     (hm : ∀ column row,((matrix.get column).get row).digits.length≤bits)
     (hi : ∀ row,(initial.get row).digits.length≤bits)
     (hp : ∀ column,(padding.get column).digits.length≤bits) (vertex : Fin (count+1)) :
     (binaryPaddedEntry count matrix initial padding permutation vertex).value.digits.length≤count+3*bits+2 := by
   have ht := IntegerBits.sumFin_length (count+1) (3*bits) (paddedProduct matrix padding (permutation.get vertex))
     (fun column => paddedProduct_length matrix padding _ column hm hp)
   have ha := IntegerBits.add_length (initial.get (permutation.get vertex))
     (IntegerBits.sumFin (count+1) (paddedProduct matrix padding (permutation.get vertex))).value
   have hi' := hi (permutation.get vertex)
   simp only [binaryPaddedEntry,readVector_value]
   omega

 def binaryPaddedEntryWork (count bits : ℕ) : ℕ :=
   6*(count+1)+(count+1)*(9*(count+1)+20*(2*bits+1)^2+20*(count+1+3*bits)+27)+20*(count+1+3*bits)+21

 theorem binaryPaddedEntry_work (count bits : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1))
     (hm : ∀ column row,((matrix.get column).get row).digits.length≤bits)
     (hi : ∀ row,(initial.get row).digits.length≤bits)
     (hp : ∀ column,(padding.get column).digits.length≤bits) (vertex : Fin (count+1)) :
     (binaryPaddedEntry count matrix initial padding permutation vertex).work≤binaryPaddedEntryWork count bits := by
   let row := (readVector 0 permutation vertex).value
   have ht := IntegerBits.sumFin_length (count+1) (3*bits) (paddedProduct matrix padding row)
     (fun column => paddedProduct_length matrix padding _ column hm hp)
   have wt := IntegerBits.sumFin_work (count+1) (3*bits) (9*(count+1)+20*(2*bits+1)^2+16)
     (paddedProduct matrix padding row) (fun column => paddedProduct_length matrix padding _ column hm hp)
     (fun column => paddedProduct_work matrix padding _ column hm hp)
   have wr := readVector_work 0 permutation vertex
   have wi := readVector_work IntegerBits.zero initial row
   have wa := IntegerBits.add_work (readVector IntegerBits.zero initial row).value
     (IntegerBits.sumFin (count+1) (paddedProduct matrix padding row)).value
   have hil : (readVector IntegerBits.zero initial row).value.digits.length≤bits := by rw [readVector_value];exact hi row
   have hmax : max (readVector IntegerBits.zero initial row).value.digits.length
       (IntegerBits.sumFin (count+1) (paddedProduct matrix padding row)).value.digits.length≤count+1+3*bits := by omega
   change (readVector 0 permutation vertex).work+(readVector IntegerBits.zero initial row).work+
     (IntegerBits.sumFin (count+1) (paddedProduct matrix padding row)).work+
     (IntegerBits.add (readVector IntegerBits.zero initial row).value
       (IntegerBits.sumFin (count+1) (paddedProduct matrix padding row)).value).work+4≤_
   unfold binaryPaddedEntryWork
   nlinarith

 def binaryPaddedLoad (count : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) : CountedValue (Vector IntegerBits (count+1)) :=
   storeData (count+1) (binaryPaddedEntry count matrix initial padding permutation)

 theorem binaryPaddedLoad_value (count : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (vertex : Fin (count+1)) :
     ((binaryPaddedLoad count matrix initial padding permutation).value.get vertex).decode=
       (initial.get (permutation.get vertex)).decode+
         ∑ column,(padding.get column).decode*((matrix.get column).get (permutation.get vertex)).decode := by
   simp only [binaryPaddedLoad,storeData_get,binaryPaddedEntry_value]

 theorem binaryPaddedLoad_length (count bits : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1))
     (hm : ∀ column row,((matrix.get column).get row).digits.length≤bits)
     (hi : ∀ row,(initial.get row).digits.length≤bits)
     (hp : ∀ column,(padding.get column).digits.length≤bits) (vertex : Fin (count+1)) :
     ((binaryPaddedLoad count matrix initial padding permutation).value.get vertex).digits.length≤count+3*bits+2 := by
   simp only [binaryPaddedLoad,storeData_get]
   exact binaryPaddedEntry_length count bits matrix initial padding permutation hm hi hp vertex

 theorem binaryPaddedLoad_work (count bits : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1))
     (hm : ∀ column row,((matrix.get column).get row).digits.length≤bits)
     (hi : ∀ row,(initial.get row).digits.length≤bits)
     (hp : ∀ column,(padding.get column).digits.length≤bits) :
     (binaryPaddedLoad count matrix initial padding permutation).work≤(count+1)*(binaryPaddedEntryWork count bits+2)+2 :=
   storeData_work _ _ _ (binaryPaddedEntry_work count bits matrix initial padding permutation hm hi hp)

end AFT.BinaryArithmetic

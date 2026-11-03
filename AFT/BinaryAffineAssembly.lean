import AFT.BinaryAffineLoads
import AFT.IntegerAffineAssembly

/-! The emitted affine matrix and offset are arrays of signed Boolean lists.
All column permutation, padding products, coordinate inversion and array
materialization are charged to the bit algorithm. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 def BinaryCoordinateResult.decode {count : ℕ} (result : BinaryCoordinateResult count) : Vector ℤ count × ℤ :=
   (result.edges.map IntegerBits.decode,result.charge.decode)

 theorem binaryRoundingInverse_decode (count : ℕ) (modulus : List Bool)
     (injection load : Vector IntegerBits (count+1)) (hq : 0<value modulus)
     (hdiv : (value modulus : ℤ) ∣ ∑ index,(load.get index).decode) :
     (binaryRoundingInverse count modulus injection load).decode=
       (roundingInverseProgram count (value modulus) (injection.map IntegerBits.decode) (load.map IntegerBits.decode)).value := by
   obtain ⟨hc,he⟩ := binaryRoundingInverse_value count modulus injection load hq hdiv
   apply Prod.ext
   · apply Vector.ext
     intro index hi
     simpa only [BinaryCoordinateResult.decode,Vector.getElem_map] using he ⟨index,hi⟩
   · exact hc

 def binaryAffineColumn (count : ℕ) (modulus : List Bool)
     (injection : Vector IntegerBits (count+1))
     (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (column : Fin (count+1)) :
     CountedValue (Vector IntegerBits count × IntegerBits) :=
   let load := binaryPermutedColumn count matrix permutation column
   let result := binaryRoundingInverse count modulus injection load.value
   ⟨(result.edges,result.charge),load.work+result.work+2⟩

 structure BinaryAffineData (count : ℕ) where
   columns : Vector (Vector IntegerBits count × IntegerBits) (count+1)
   offset : Vector IntegerBits count × IntegerBits
   work : ℕ

 def binaryAffineAssembly (count : ℕ) (modulus : List Bool)
     (injection : Vector IntegerBits (count+1))
     (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) : BinaryAffineData count :=
   let columns := storeData (count+1) (binaryAffineColumn count modulus injection matrix permutation)
   let load := binaryPaddedLoad count matrix initial padding permutation
   let offset := binaryRoundingInverse count modulus injection load.value
   ⟨columns.value,(offset.edges,offset.charge),columns.work+load.work+offset.work+3⟩

 def decodeCoordinate {count : ℕ} (point : Vector IntegerBits count × IntegerBits) : Vector ℤ count × ℤ :=
   (point.1.map IntegerBits.decode,point.2.decode)

 theorem binaryAffineAssembly_value (count : ℕ) (modulus : List Bool)
     (injection : Vector IntegerBits (count+1))
     (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (hq : 0<value modulus)
     (hcolumns : ∀ column,(value modulus : ℤ) ∣ ∑ vertex,((matrix.get column).get (permutation.get vertex)).decode)
     (hoffset : (value modulus : ℤ) ∣ ∑ vertex,((initial.get (permutation.get vertex)).decode+
       ∑ column,(padding.get column).decode*((matrix.get column).get (permutation.get vertex)).decode)) :
     let binary := binaryAffineAssembly count modulus injection matrix initial padding permutation
     let original := integerAffineAssembly count (value modulus) (injection.map IntegerBits.decode)
       (matrix.map (Vector.map IntegerBits.decode)) (initial.map IntegerBits.decode) (padding.map IntegerBits.decode) permutation
     binary.columns.map decodeCoordinate=original.columns ∧ decodeCoordinate binary.offset=original.offset := by
   constructor
   · apply Vector.ext
     intro column hc
     simp only [Vector.getElem_map]
     change decodeCoordinate ((storeData _ (binaryAffineColumn count modulus injection matrix permutation)).value.get ⟨column,hc⟩)=_
     rw [storeData_get]
     have he := binaryRoundingInverse_decode count modulus injection
       (binaryPermutedColumn count matrix permutation ⟨column,hc⟩).value hq (by
         simpa only [binaryPermutedColumn_value] using hcolumns ⟨column,hc⟩)
     change (binaryRoundingInverse count modulus injection (binaryPermutedColumn count matrix permutation ⟨column,hc⟩).value).decode=_
     rw [he]
     simp only [integerAffineAssembly,Vector.get_map,Vector.get_ofFn,Vector.getElem_map,Vector.getElem_ofFn]
     congr 2
     apply Vector.ext
     intro vertex hv
     change ((binaryPermutedColumn count matrix permutation ⟨column,hc⟩).value.map IntegerBits.decode).get ⟨vertex,hv⟩=_
     simp only [Vector.get_map,Vector.getElem_ofFn,binaryPermutedColumn_value]
   · have he := binaryRoundingInverse_decode count modulus injection
       (binaryPaddedLoad count matrix initial padding permutation).value hq (by
         simpa only [binaryPaddedLoad_value] using hoffset)
     change (binaryRoundingInverse count modulus injection (binaryPaddedLoad count matrix initial padding permutation).value).decode=_
     rw [he]
     simp only [integerAffineAssembly,Vector.get_map,Vector.get_ofFn]
     congr 2
     apply Vector.ext
     intro vertex hv
     change ((binaryPaddedLoad count matrix initial padding permutation).value.map IntegerBits.decode).get ⟨vertex,hv⟩=_
     simp only [Vector.get_map,Vector.getElem_ofFn,binaryPaddedLoad_value]

 def binaryAffineAssemblyWork (count modulusBits bits : ℕ) : ℕ :=
   (count+1)*((count+1)*(9*(count+1)+15)+2+binaryRoundingInverseWork count modulusBits bits+4)+2+
     ((count+1)*(binaryPaddedEntryWork count bits+2)+2)+
     binaryRoundingInverseWork count modulusBits (count+3*bits+2)+3

 theorem binaryAffineAssembly_work (count bits : ℕ) (modulus : List Bool)
     (injection : Vector IntegerBits (count+1))
     (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (initial padding : Vector IntegerBits (count+1))
     (permutation : Vector (Fin (count+1)) (count+1))
     (hinjection : ∀ row,(injection.get row).digits.length≤bits)
     (hm : ∀ column row,((matrix.get column).get row).digits.length≤bits)
     (hi : ∀ row,(initial.get row).digits.length≤bits)
     (hp : ∀ column,(padding.get column).digits.length≤bits) :
     (binaryAffineAssembly count modulus injection matrix initial padding permutation).work≤
       binaryAffineAssemblyWork count modulus.length bits := by
   have hc (column : Fin (count+1)) : (binaryAffineColumn count modulus injection matrix permutation column).work≤
       (count+1)*(9*(count+1)+15)+2+binaryRoundingInverseWork count modulus.length bits+2 := by
     have hw := binaryPermutedColumn_work count matrix permutation column
     have hr := binaryRoundingInverse_work count bits modulus injection
       (binaryPermutedColumn count matrix permutation column).value hinjection
       (by intro row;rw [binaryPermutedColumn_value];exact hm column _)
     change _+_+2≤_
     omega
   have hcolumns := storeData_work (count+1) _ _ hc
   have hload := binaryPaddedLoad_work count bits matrix initial padding permutation hm hi hp
   have hoffset := binaryRoundingInverse_work count (count+3*bits+2) modulus injection
     (binaryPaddedLoad count matrix initial padding permutation).value
     (fun row => (hinjection row).trans (by omega))
     (binaryPaddedLoad_length count bits matrix initial padding permutation hm hi hp)
   simp only [binaryAffineAssembly,binaryAffineAssemblyWork]
   nlinarith

end AFT.BinaryArithmetic

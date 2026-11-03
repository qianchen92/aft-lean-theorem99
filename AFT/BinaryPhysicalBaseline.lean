import AFT.BinaryBlockAddresses
import AFT.BinaryIntegerData
import AFT.PhysicalLoadProgram

/-! Physical initial loads and the shared queue injection are generated from
stored chart/baseline/center data using their actual arithmetic block addresses. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 def IntegerBits.one : IntegerBits := ⟨false,[true]⟩
 @[simp] theorem IntegerBits.one_value : IntegerBits.one.decode=1 := rfl

 def binaryPhysicalVertex (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (vertex : Fin (count+1)) : CountedValue (Sigma (blockSlotsProgram legs rest)) :=
   binaryVertexCode legs rest (Fin.cast hvertex.symm vertex)

 theorem binaryPhysicalVertex_value (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (vertex : Fin (count+1)) :
     (binaryPhysicalVertex legs rest count hvertex vertex).value=
       (physicalVertexNumberingProgram legs rest count hvertex).symm vertex :=
   binaryVertexCode_value legs rest _

 def binaryRootRead (legs rest : ℕ) (data : Vector IntegerBits (legs+rest)) (index : Fin legs⊕Fin rest) :
     CountedValue IntegerBits :=
   let address := binaryRootAddress legs rest index
   let result := readVector IntegerBits.zero data address.value
   ⟨result.value,address.work+result.work+2⟩

 theorem binaryRootRead_value (legs rest : ℕ) (data : Vector IntegerBits (legs+rest)) (index : Fin legs⊕Fin rest) :
     (binaryRootRead legs rest data index).value=data.get (blockNumbering legs rest index) := by
   simp only [binaryRootRead,readVector_value,binaryRootAddress_value]

 theorem binaryRootRead_work (legs rest : ℕ) (data : Vector IntegerBits (legs+rest)) (index : Fin legs⊕Fin rest) :
     (binaryRootRead legs rest data index).work≤2*legs+3*(legs+rest)+8 := by
   have ha := binaryRootAddress_work legs rest index
   have hr := readVector_work IntegerBits.zero data (binaryRootAddress legs rest index).value
   simp only [binaryRootRead]
   omega

 private def initialBlockEntry (legs rest : ℕ) (modulus : IntegerBits) (shift baseline : Vector IntegerBits legs)
     (center : Vector IntegerBits (legs+rest)) : (Sigma (blockSlotsProgram legs rest))→ CountedValue IntegerBits
   | ⟨.inl leg,slot⟩ =>
       let translated := readVector IntegerBits.zero shift leg
       let anchored := readVector IntegerBits.zero baseline leg
       let body := binaryRootRead legs rest center (.inl leg)
       let reduced := IntegerBits.subtract modulus IntegerBits.one
       let shifted := IntegerBits.add reduced.value anchored.value
       let complement := IntegerBits.subtract shifted.value translated.value
       ⟨![translated.value,complement.value,body.value] slot,
         translated.work+anchored.work+body.work+reduced.work+shifted.work+complement.work+8⟩
   | ⟨.inr body,_⟩ => binaryRootRead legs rest center (.inr body)

 private theorem initialBlockEntry_value (legs rest : ℕ) (modulus : IntegerBits) (shift baseline : Vector IntegerBits legs)
     (center : Vector IntegerBits (legs+rest)) (point : Sigma (blockSlotsProgram legs rest)) :
     (initialBlockEntry legs rest modulus shift baseline center point).value.decode=
       match point with
       | ⟨.inl leg,slot⟩ => ![(shift.get leg).decode,modulus.decode-1+(baseline.get leg).decode-(shift.get leg).decode,
           (center.get (blockNumbering legs rest (.inl leg))).decode] slot
       | ⟨.inr body,slot⟩ => ![(center.get (blockNumbering legs rest (.inr body))).decode] slot := by
   rcases point with ⟨leg|body,slot⟩
   · change Fin 3 at slot
     fin_cases slot <;> simp [initialBlockEntry,IntegerBits.subtract_value,IntegerBits.add_value,
       readVector_value,binaryRootRead_value]
   · change Fin 1 at slot
     fin_cases slot
     simp [initialBlockEntry,binaryRootRead_value]

 def binaryPhysicalInitialLoad (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (modulus : IntegerBits) (shift baseline : Vector IntegerBits legs) (center : Vector IntegerBits (legs+rest)) :
     CountedValue (Vector IntegerBits (count+1)) :=
   storeData (count+1) (fun vertex =>
     let point := binaryPhysicalVertex legs rest count hvertex vertex
     let result := initialBlockEntry legs rest modulus shift baseline center point.value
     ⟨result.value,point.work+result.work+2⟩)

 theorem binaryPhysicalInitialLoad_value (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (modulus : IntegerBits) (shift baseline : Vector IntegerBits legs) (center : Vector IntegerBits (legs+rest))
     (vertex : Fin (count+1)) :
     ((binaryPhysicalInitialLoad legs rest count hvertex modulus shift baseline center).value.get vertex).decode=
       (physicalInitialLoadProgram legs rest count hvertex modulus.decode (shift.map IntegerBits.decode)
         (baseline.map IntegerBits.decode) (center.map IntegerBits.decode)).value.get vertex := by
   simp only [binaryPhysicalInitialLoad,storeData_get,initialBlockEntry_value,binaryPhysicalVertex_value,
     physicalInitialLoadProgram,Vector.get_ofFn,Vector.get_map]
   rcases (physicalVertexNumberingProgram legs rest count hvertex).symm vertex with ⟨leg|body,slot⟩ <;> rfl

 private def queueBlockEntry (legs rest : ℕ) (mask : Vector IntegerBits (legs+rest)) :
     (Sigma (blockSlotsProgram legs rest))→ CountedValue IntegerBits
   | ⟨.inl leg,slot⟩ =>
       let body := binaryRootRead legs rest mask (.inl leg)
       ⟨![IntegerBits.zero,IntegerBits.zero,body.value] slot,body.work+4⟩
   | ⟨.inr body,_⟩ => binaryRootRead legs rest mask (.inr body)

 private theorem queueBlockEntry_value (legs rest : ℕ) (mask : Vector IntegerBits (legs+rest))
     (point : Sigma (blockSlotsProgram legs rest)) :
     (queueBlockEntry legs rest mask point).value.decode=
       match point with
       | ⟨.inl leg,slot⟩ => ![0,0,(mask.get (blockNumbering legs rest (.inl leg))).decode] slot
       | ⟨.inr body,slot⟩ => ![(mask.get (blockNumbering legs rest (.inr body))).decode] slot := by
   rcases point with ⟨leg|body,slot⟩
   · change Fin 3 at slot
     fin_cases slot <;> simp [queueBlockEntry,binaryRootRead_value]
   · change Fin 1 at slot
     fin_cases slot
     simp [queueBlockEntry,binaryRootRead_value]

 def binaryPhysicalQueueLoad (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (mask : Vector IntegerBits (legs+rest)) : CountedValue (Vector IntegerBits (count+1)) :=
   storeData (count+1) (fun vertex =>
     let point := binaryPhysicalVertex legs rest count hvertex vertex
     let result := queueBlockEntry legs rest mask point.value
     ⟨result.value,point.work+result.work+2⟩)

 theorem binaryPhysicalQueueLoad_value (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (mask : Vector IntegerBits (legs+rest)) (vertex : Fin (count+1)) :
     ((binaryPhysicalQueueLoad legs rest count hvertex mask).value.get vertex).decode=
       (physicalQueueLoadProgram legs rest count hvertex (mask.map IntegerBits.decode)).value.get vertex := by
   simp only [binaryPhysicalQueueLoad,storeData_get,queueBlockEntry_value,binaryPhysicalVertex_value,
     physicalQueueLoadProgram,Vector.get_ofFn,Vector.get_map]
   rcases (physicalVertexNumberingProgram legs rest count hvertex).symm vertex with ⟨leg|body,slot⟩ <;> rfl


 private theorem initialBlockEntry_length (legs rest bits : ℕ) (modulus : IntegerBits)
     (shift baseline : Vector IntegerBits legs) (center : Vector IntegerBits (legs+rest))
     (hm : modulus.digits.length≤bits) (hs : ∀ leg,(shift.get leg).digits.length≤bits)
     (hb : ∀ leg,(baseline.get leg).digits.length≤bits)
     (hc : ∀ index,(center.get index).digits.length≤bits) (point : Sigma (blockSlotsProgram legs rest)) :
     (initialBlockEntry legs rest modulus shift baseline center point).value.digits.length≤bits+4 := by
   rcases point with ⟨leg|body,slot⟩
   · have hr := IntegerBits.subtract_length modulus IntegerBits.one
     have ha := IntegerBits.add_length (IntegerBits.subtract modulus IntegerBits.one).value (baseline.get leg)
     have hd := IntegerBits.subtract_length
       (IntegerBits.add (IntegerBits.subtract modulus IntegerBits.one).value (baseline.get leg)).value (shift.get leg)
     have hs' := hs leg
     have hb' := hb leg
     have hc' := hc (blockNumbering legs rest (.inl leg))
     have ho : IntegerBits.one.digits.length=1 := rfl
     change Fin 3 at slot
     fin_cases slot <;> simp only [initialBlockEntry,readVector_value,binaryRootRead_value,
       Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> omega
   · simpa only [initialBlockEntry,binaryRootRead_value] using (hc (blockNumbering legs rest (.inr body))).trans (by omega)

 private theorem initialBlockEntry_work (legs rest bits : ℕ) (modulus : IntegerBits)
     (shift baseline : Vector IntegerBits legs) (center : Vector IntegerBits (legs+rest))
     (hm : modulus.digits.length≤bits) (hs : ∀ leg,(shift.get leg).digits.length≤bits)
     (hb : ∀ leg,(baseline.get leg).digits.length≤bits) (point : Sigma (blockSlotsProgram legs rest)) :
     (initialBlockEntry legs rest modulus shift baseline center point).work≤20*(legs+rest+1)+100*(bits+5) := by
   rcases point with ⟨leg|body,slot⟩
   · have wr := readVector_work IntegerBits.zero shift leg
     have wb := readVector_work IntegerBits.zero baseline leg
     have wc := binaryRootRead_work legs rest center (.inl leg)
     have lr := IntegerBits.subtract_length modulus IntegerBits.one
     have la := IntegerBits.add_length (IntegerBits.subtract modulus IntegerBits.one).value (baseline.get leg)
     have ws := IntegerBits.subtract_work modulus IntegerBits.one
     have wa := IntegerBits.add_work (IntegerBits.subtract modulus IntegerBits.one).value (baseline.get leg)
     have wd := IntegerBits.subtract_work
       (IntegerBits.add (IntegerBits.subtract modulus IntegerBits.one).value (baseline.get leg)).value (shift.get leg)
     have hs' := hs leg
     have hb' := hb leg
     have ho : IntegerBits.one.digits.length=1 := rfl
     simp only [initialBlockEntry,readVector_value]
     omega
   · exact (binaryRootRead_work legs rest center (.inr body)).trans (by omega)

 theorem binaryPhysicalInitialLoad_length (legs rest count bits : ℕ) (hvertex : legs*3+rest=count+1)
     (modulus : IntegerBits) (shift baseline : Vector IntegerBits legs) (center : Vector IntegerBits (legs+rest))
     (hm : modulus.digits.length≤bits) (hs : ∀ leg,(shift.get leg).digits.length≤bits)
     (hb : ∀ leg,(baseline.get leg).digits.length≤bits)
     (hc : ∀ index,(center.get index).digits.length≤bits) (vertex : Fin (count+1)) :
     ((binaryPhysicalInitialLoad legs rest count hvertex modulus shift baseline center).value.get vertex).digits.length≤bits+4 := by
   simp only [binaryPhysicalInitialLoad,storeData_get]
   exact initialBlockEntry_length legs rest bits modulus shift baseline center hm hs hb hc _

 theorem binaryPhysicalInitialLoad_work (legs rest count bits : ℕ) (hvertex : legs*3+rest=count+1)
     (modulus : IntegerBits) (shift baseline : Vector IntegerBits legs) (center : Vector IntegerBits (legs+rest))
     (hm : modulus.digits.length≤bits) (hs : ∀ leg,(shift.get leg).digits.length≤bits)
     (hb : ∀ leg,(baseline.get leg).digits.length≤bits) :
     (binaryPhysicalInitialLoad legs rest count hvertex modulus shift baseline center).work≤
       (count+1)*(1000*(count+7)^2+20*(count+2)+100*(bits+5)+4)+2 := by
   apply storeData_work
   intro vertex
   have hv := binaryVertexCode_work legs rest (Fin.cast hvertex.symm vertex)
   have hi := initialBlockEntry_work legs rest bits modulus shift baseline center hm hs hb
     (binaryPhysicalVertex legs rest count hvertex vertex).value
   have he : legs*3+rest+6=count+7 := by omega
   rw [he] at hv
   change (binaryPhysicalVertex legs rest count hvertex vertex).work≤_ at hv
   dsimp only
   have hh : legs+rest≤count+1 := by omega
   omega

 private theorem queueBlockEntry_length (legs rest bits : ℕ) (mask : Vector IntegerBits (legs+rest))
     (hm : ∀ index,(mask.get index).digits.length≤bits) (point : Sigma (blockSlotsProgram legs rest)) :
     (queueBlockEntry legs rest mask point).value.digits.length≤bits := by
   rcases point with ⟨leg|body,slot⟩
   · change Fin 3 at slot
     fin_cases slot <;> simp only [queueBlockEntry,binaryRootRead_value,Matrix.cons_val_zero',Matrix.cons_val_succ',IntegerBits.zero,List.length_nil] <;> first | omega | exact hm _
   · exact by simpa only [queueBlockEntry,binaryRootRead_value] using hm (blockNumbering legs rest (.inr body))

 private theorem queueBlockEntry_work (legs rest : ℕ) (mask : Vector IntegerBits (legs+rest))
     (point : Sigma (blockSlotsProgram legs rest)) :
     (queueBlockEntry legs rest mask point).work≤8*(legs+rest+1)+4 := by
   rcases point with ⟨leg|body,slot⟩
   · have hh := binaryRootRead_work legs rest mask (.inl leg)
     simp only [queueBlockEntry]
     omega
   · exact (binaryRootRead_work legs rest mask (.inr body)).trans (by omega)

 theorem binaryPhysicalQueueLoad_length (legs rest count bits : ℕ) (hvertex : legs*3+rest=count+1)
     (mask : Vector IntegerBits (legs+rest)) (hm : ∀ index,(mask.get index).digits.length≤bits)
     (vertex : Fin (count+1)) :
     ((binaryPhysicalQueueLoad legs rest count hvertex mask).value.get vertex).digits.length≤bits := by
   simp only [binaryPhysicalQueueLoad,storeData_get]
   exact queueBlockEntry_length legs rest bits mask hm _

 theorem binaryPhysicalQueueLoad_work (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (mask : Vector IntegerBits (legs+rest)) :
     (binaryPhysicalQueueLoad legs rest count hvertex mask).work≤(count+1)*(1000*(count+7)^2+10*count+24)+2 := by
   apply storeData_work
   intro vertex
   have hv := binaryVertexCode_work legs rest (Fin.cast hvertex.symm vertex)
   have hi := queueBlockEntry_work legs rest mask (binaryPhysicalVertex legs rest count hvertex vertex).value
   have he : legs*3+rest+6=count+7 := by omega
   rw [he] at hv
   change (binaryPhysicalVertex legs rest count hvertex vertex).work≤_ at hv
   dsimp only
   have hh : legs+rest≤count+1 := by omega
   omega

end AFT.BinaryArithmetic

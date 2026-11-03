import AFT.BinaryCounterDivision
import AFT.BinaryPublicPoolScan
import AFT.FiniteBlockNumbering

/-! Runtime block decoding and edge/root addressing use bounded unary
comparisons, long division and explicitly charged counter arithmetic. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 def binaryVertexCode (legs rest : ℕ) (index : Fin (legs*3+rest)) :
     CountedValue (Sigma (blockSlotsProgram legs rest)) :=
   let boundary := multiplyCounter legs 3
   let selected := lessCounter index.val boundary.count
   if h : selected.value=true then
     let qr := divideCounter index.val 3
     ⟨⟨.inl ⟨qr.quotient,by
         have hi := (lessCounter_value _ _).mp h
         simp only [boundary,multiplyCounter_value] at hi
         rw [(divideCounter_value _ _ (by omega)).1]
         exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hi⟩,
       ⟨qr.remainder,by
         change qr.remainder < 3
         rw [(divideCounter_value _ _ (by omega)).2]
         exact Nat.mod_lt _ (by omega)⟩⟩,
       boundary.work+selected.work+qr.work+4⟩
   else
     let body := differenceCounter index.val boundary.count
     ⟨⟨.inr ⟨body.count,by
         rw [differenceCounter_value]
         have hi : ¬index.val<boundary.count := fun hi => h ((lessCounter_value _ _).mpr hi)
         have hb : boundary.count=legs*3 := multiplyCounter_value legs 3
         omega⟩,(0 : Fin 1)⟩,boundary.work+selected.work+body.work+4⟩

 theorem binaryVertexCode_value (legs rest : ℕ) (index : Fin (legs*3+rest)) :
     (binaryVertexCode legs rest index).value=(blockVertexNumbering legs rest).symm index := by
   apply (blockVertexNumbering legs rest).injective
   rw [Equiv.apply_symm_apply]
   unfold binaryVertexCode
   dsimp only
   split
   · rename_i h
     apply Fin.ext
     change (divideCounter index.val 3).remainder+3*(divideCounter index.val 3).quotient=index.val
     rw [(divideCounter_value index.val 3 (by omega)).1,(divideCounter_value index.val 3 (by omega)).2]
     exact Nat.mod_add_div _ _
   · rename_i h
     apply Fin.ext
     change legs*3+(0+1*(differenceCounter index.val (multiplyCounter legs 3).count).count)=index.val
     simp only [Nat.zero_add,Nat.one_mul]
     rw [differenceCounter_value,multiplyCounter_value]
     have hi : legs*3 ≤ index.val := by
       have hh : ¬ index.val<(multiplyCounter legs 3).count := fun hi => h ((lessCounter_value _ _).mpr hi)
       rw [multiplyCounter_value] at hh
       omega
     omega

 set_option maxRecDepth 4096 in
 theorem binaryVertexCode_work (legs rest : ℕ) (index : Fin (legs*3+rest)) :
     (binaryVertexCode legs rest index).work≤1000*(legs*3+rest+6)^2 := by
   have hm := multiplyCounter_work legs 3
   have hl := lessCounter_work_left index.val (multiplyCounter legs 3).count
   have hd := divideCounter_work index.val 3 (by omega)
   have hs := differenceCounter_work index.val (multiplyCounter legs 3).count
   have hi := index.isLt
   have hdb : 500*(index.val+3+2)^2≤500*(legs*3+rest+6)^2 := by gcongr;omega
   unfold binaryVertexCode
   dsimp only
   split
   · change (multiplyCounter legs 3).work+(lessCounter index.val (multiplyCounter legs 3).count).work+
       (divideCounter index.val 3).work+4≤_
     nlinarith only [hm,hl,hd,hdb,hi,Nat.zero_le legs,Nat.zero_le rest]
   · change (multiplyCounter legs 3).work+(lessCounter index.val (multiplyCounter legs 3).count).work+
       (differenceCounter index.val (multiplyCounter legs 3).count).work+4≤_
     nlinarith only [hm,hl,hs,hi,Nat.zero_le legs,Nat.zero_le rest]

 def binaryRootAddress (legs rest : ℕ) : (Fin legs⊕Fin rest)→ CountedValue (Fin (legs+rest))
   | .inl leg => ⟨⟨leg.val,by omega⟩,1⟩
   | .inr body =>
       let address := addCounter legs body.val
       ⟨⟨address.count,by rw [addCounter_value];omega⟩,address.work+2⟩

 theorem binaryRootAddress_value (legs rest : ℕ) (index : Fin legs⊕Fin rest) :
     (binaryRootAddress legs rest index).value=blockNumbering legs rest index := by
   cases index <;> apply Fin.ext <;> simp [binaryRootAddress,blockNumbering,addCounter_value]

 theorem binaryRootAddress_work (legs rest : ℕ) (index : Fin legs⊕Fin rest) :
     (binaryRootAddress legs rest index).work≤2*legs+3 := by
   cases index <;> simp only [binaryRootAddress,addCounter_work] <;> omega

 def binaryEdgeAddress (legs body : ℕ) : ((Fin legs×Fin 2)⊕Fin body)→ CountedValue (Fin (legs*2+body))
   | .inl edge =>
       let doubled := doubleCounter edge.1.val
       let address := addCounter edge.2.val doubled.count
       ⟨⟨address.count,by rw [addCounter_value,doubleCounter_value];omega⟩,doubled.work+address.work+3⟩
   | .inr edge =>
       let doubled := doubleCounter legs
       let address := addCounter doubled.count edge.val
       ⟨⟨address.count,by rw [addCounter_value,doubleCounter_value];omega⟩,doubled.work+address.work+3⟩

 theorem binaryEdgeAddress_value (legs body : ℕ) (index : (Fin legs×Fin 2)⊕Fin body) :
     (binaryEdgeAddress legs body index).value=blockEdgeNumbering legs body index := by
   cases index <;> apply Fin.ext <;>
     simp [binaryEdgeAddress,blockEdgeNumbering,addCounter_value,doubleCounter_value,finProdFinEquiv]
   omega

 theorem binaryEdgeAddress_work (legs body : ℕ) (index : (Fin legs×Fin 2)⊕Fin body) :
     (binaryEdgeAddress legs body index).work≤7*legs+9 := by
   cases index with
   | inl edge =>
       have he := edge.1.isLt
       have hs := edge.2.isLt
       simp only [binaryEdgeAddress,addCounter_work,doubleCounter_work,doubleCounter_value]
       omega
   | inr edge => simp only [binaryEdgeAddress,addCounter_work,doubleCounter_work,doubleCounter_value];omega

end AFT.BinaryArithmetic

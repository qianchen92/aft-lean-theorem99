import AFT.BinaryChartArray

/-! Sequential materialization for finite metadata arrays. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

 def storeData {α : Type*} (count : ℕ) (term : Fin count → CountedValue α) : CountedValue (Vector α count) :=
   let computed := Vector.ofFn term
   ⟨computed.map (fun entry => entry.value),(∑ index,(computed.get index).work)+2*count+2⟩

 theorem storeData_get {α : Type*} (count : ℕ) (term : Fin count → CountedValue α) (index : Fin count) :
     (storeData count term).value.get index=(term index).value := by
   simp only [storeData,Vector.get_map,Vector.get_ofFn]

 theorem storeData_work {α : Type*} (count bound : ℕ) (term : Fin count → CountedValue α)
     (h : ∀ index,(term index).work≤bound) :
     (storeData count term).work≤count*(bound+2)+2 := by
   have hs := Finset.sum_le_sum (s:=Finset.univ) (fun index _ => h index)
   simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
   simp only [storeData,Vector.get_ofFn]
   nlinarith

end AFT.BinaryArithmetic

import AFT.BinaryChartIteration

/-! # Materialized binary rational matrix arrays -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
open scoped BigOperators

structure MatrixResult (count : ℕ) where
  data : Vector (Vector RationalBits count) count
  work : ℕ

def buildRows (count : ℕ) (row : Fin count → ArrayResult count) : MatrixResult count :=
  let computed := Vector.ofFn row
  ⟨computed.map (fun result => result.data),(∑ index,(computed.get index).work)+2*count+2⟩

theorem buildRows_get (count : ℕ) (row : Fin count → ArrayResult count) (index : Fin count) :
    (buildRows count row).data.get index=(row index).data := by simp [buildRows]

theorem buildRows_work (count budget : ℕ) (row : Fin count → ArrayResult count)
    (h : ∀ index,(row index).work≤budget) :
    (buildRows count row).work≤count*(budget+2)+2 := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun index _ => h index)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  simp only [buildRows,Vector.get_ofFn]
  nlinarith

def buildMatrix (count : ℕ) (entry : Fin count → Fin count → RationalResult) : MatrixResult count :=
  buildRows count (fun row => buildArray count (entry row))

theorem buildMatrix_get (count : ℕ) (entry : Fin count → Fin count → RationalResult) (row column : Fin count) :
    ((buildMatrix count entry).data.get row).get column=(entry row column).data := by
  simp only [buildMatrix,buildRows_get,buildArray_get]

theorem buildMatrix_work (count budget : ℕ) (entry : Fin count → Fin count → RationalResult)
    (h : ∀ row column,(entry row column).work≤budget) :
    (buildMatrix count entry).work≤count*(count*(budget+2)+4)+2 :=
  buildRows_work count (count*(budget+2)+2) _ (fun row => buildArray_work count budget _ (h row))

def transposeMatrix {count : ℕ} (matrix : Vector (Vector RationalBits count) count) : MatrixResult count :=
  buildMatrix count (fun row column =>
    let entry := matrixEntry matrix column row
    ⟨entry.value,entry.work+1⟩)

theorem transposeMatrix_get {count : ℕ} (matrix : Vector (Vector RationalBits count) count) (row column : Fin count) :
    ((transposeMatrix matrix).data.get row).get column=(matrix.get column).get row := by
  simp only [transposeMatrix,buildMatrix_get,matrixEntry_value]

theorem transposeMatrix_work {count : ℕ} (matrix : Vector (Vector RationalBits count) count) :
    (transposeMatrix matrix).work≤count*(count*(7*count+11)+4)+2 := by
  apply buildMatrix_work count (7*count+9)
  intro row column
  dsimp only
  have hh := matrixEntry_work matrix column row
  omega

end AFT.BinaryArithmetic.RationalBits

import AFT.BinaryChartArray
import AFT.BinaryDataArrays

/-! Stored finite palette words are copied to natural-query buffers by actual reads. -/
namespace CurrentAFT.BinaryNaturalCoordinates
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

def current {base count : ℕ} (hb : 0<base) (word : Vector (Fin base) count) : CountedValue (Vector ℕ count) :=
  storeData count (fun index =>
    let read := readVector ⟨0,hb⟩ word index
    ⟨read.value.val,read.work+1⟩)

theorem current_get {base count : ℕ} (hb : 0<base) (word : Vector (Fin base) count) (index : Fin count) :
    (current hb word).value.get index=(word.get index).val := by
  simp only [current,storeData_get,readVector_value]

theorem current_valid {base count : ℕ} (hb : 0<base) (word : Vector (Fin base) count) (index : Fin count) :
    (current hb word).value.get index<base := by
  rw [current_get]
  exact (word.get index).isLt

theorem current_work {base count : ℕ} (hb : 0<base) (word : Vector (Fin base) count) :
    (current hb word).work≤count*(3*count+6)+2 := by
  apply storeData_work count (3*count+4)
  intro index
  have h := readVector_work (⟨0,hb⟩:Fin base) word index
  change _+1≤_
  omega

end CurrentAFT.BinaryNaturalCoordinates

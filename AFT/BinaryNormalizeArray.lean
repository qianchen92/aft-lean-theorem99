import AFT.BinaryChartArray

/-! # Actual binary normalization of a stored finite rational array

The normalizer is accumulated once, then reused by every entry. Array reads
use the explicit sequential lookup program. No unbounded rational operation
or array lookup is charged as one step.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
open scoped BigOperators

def sumArray {count : ℕ} (input : Vector RationalBits count) : RationalResult :=
  sumFin count (fun index => let found := readVector zero input index;⟨found.value,found.work⟩)

theorem sumArray_value {count : ℕ} (input : Vector RationalBits count) :
    (sumArray input).data.decode=∑ index,(input.get index).decode := by
  simp only [sumArray,sumFin_value,readVector_value]

theorem sumArray_height {count : ℕ} (input : Vector RationalBits count) (bits : ℕ)
    (hh : ∀ index,HeightBound (input.get index).decode bits) :
    HeightBound (sumArray input).data.decode (count*(bits+1)) :=
  sumFin_height count bits _ (fun index => by simp only [readVector_value];exact hh index)

def sumArrayWork (count bits : ℕ) : ℕ :=
  count*(3*count+3+primitiveWorkBound ((count+1)*(bits+1))+2)+2

theorem sumArray_work {count : ℕ} (input : Vector RationalBits count) (bits : ℕ)
    (hh : ∀ index,HeightBound (input.get index).decode bits) : (sumArray input).work≤ sumArrayWork count bits :=
  sumFin_work count bits (3*count+3) _
    (fun index => by simp only [readVector_value];exact hh index)
    (fun index => readVector_work zero input index)

def normalizeArray {count : ℕ} (input : Vector RationalBits count) : ArrayResult count :=
  let total := sumArray input
  let output := buildArray count (fun index =>
    let numerator := readVector zero input index
    let result := quotient numerator.value total.data
    ⟨result.data,numerator.work+result.work+2⟩)
  ⟨output.data,total.work+output.work+2⟩

theorem normalizeArray_value {count : ℕ} (input : Vector RationalBits count) (index : Fin count) :
    ((normalizeArray input).data.get index).decode=
      (input.get index).decode/(∑ point,(input.get point).decode) := by
  simp only [normalizeArray,buildArray_get,quotient_value,readVector_value,sumArray_value]

theorem normalizeArray_height {count : ℕ} (input : Vector RationalBits count) (bits : ℕ)
    (hh : ∀ index,HeightBound (input.get index).decode bits) (index : Fin count) :
    HeightBound ((normalizeArray input).data.get index).decode (bits+count*(bits+1)) := by
  rw [normalizeArray_value,← sumArray_value]
  exact (hh index).div (sumArray_height input bits hh)

def normalizeArrayWork (count bits : ℕ) : ℕ :=
  sumArrayWork count bits+count*(3*count+3+2*primitiveWorkBound (bits+count*(bits+1))+6)+4

theorem normalizeArray_work {count : ℕ} (input : Vector RationalBits count) (bits : ℕ)
    (hh : ∀ index,HeightBound (input.get index).decode bits) :
    (normalizeArray input).work≤ normalizeArrayWork count bits := by
  have ht := sumArray_height input bits hh
  have wt := sumArray_work input bits hh
  have hentry (index : Fin count) :
      (readVector zero input index).work+
        (quotient (readVector zero input index).value (sumArray input).data).work+2≤
          3*count+3+2*primitiveWorkBound (bits+count*(bits+1))+4 := by
    have wr := readVector_work zero input index
    have wq := quotient_work (readVector zero input index).value (sumArray input).data
      (bits+count*(bits+1))
      (by rw [readVector_value];exact (hh index).mono (Nat.le_add_right _ _))
      (ht.mono (Nat.le_add_left _ _))
    omega
  have wo := buildArray_work count (3*count+3+2*primitiveWorkBound (bits+count*(bits+1))+4)
    (fun index => let numerator := readVector zero input index;let result := quotient numerator.value (sumArray input).data;
      ⟨result.data,numerator.work+result.work+2⟩) hentry
  dsimp only at wo
  simp only [normalizeArray,normalizeArrayWork]
  nlinarith

end AFT.BinaryArithmetic.RationalBits

import AFT.BinaryNormalizeArray
import AFT.BinaryRationalControl
import AFT.RationalPositiveNormalizeHeight

/-! # Positive normalization with actual binary arithmetic

Clipping inspects the sign bit. The exceptional zero-normalizer branch tests
the canonical numerator's list constructor. Both branches materialize their
output, and every sequential array read and rational operation is charged.
-/
set_option maxRecDepth 2048

namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
open scoped BigOperators

theorem numerator_empty_iff (input : RationalBits) : input.numerator=[] ↔ input.decode=0 := by
  have hn := input.numerator_normal
  have hv : value input.numerator=0 ↔ input.decode=0 := by
    rw [← signedValue_natAbs input.negative input.numerator,Int.natAbs_eq_zero,← decode_num,Rat.num_eq_zero]
  constructor
  · intro hh
    apply hv.mp
    rw [hh]
    rfl
  · intro hh
    have hz := hv.mpr hh
    rw [hz] at hn
    exact List.length_eq_zero_iff.mp (by simpa using hn)

def positiveArray {count : ℕ} (input : Vector RationalBits count) : ArrayResult count :=
  buildArray count (fun index =>
    let found := readVector zero input index
    let result := maxZero found.value
    ⟨result.data,found.work+result.work+2⟩)

theorem positiveArray_value {count : ℕ} (input : Vector RationalBits count) (index : Fin count) :
    ((positiveArray input).data.get index).decode=max 0 (input.get index).decode := by
  simp only [positiveArray,buildArray_get,maxZero_value,readVector_value,max_comm]

theorem positiveArray_height {count : ℕ} (input : Vector RationalBits count) (height : ℕ)
    (hh : ∀ index,HeightBound (input.get index).decode height) (index : Fin count) :
    HeightBound ((positiveArray input).data.get index).decode height := by
  rw [positiveArray_value,max_comm]
  exact max_zero_height _ _ (hh index)

theorem positiveArray_work {count : ℕ} (input : Vector RationalBits count) :
    (positiveArray input).work≤ count*(3*count+9)+2 := by
  apply buildArray_work count (3*count+7)
  intro index
  have hw := readVector_work zero input index
  simp only [maxZero_work]
  omega

def binaryPositiveNormalize {count : ℕ} (input : Vector RationalBits (count+1)) : ArrayResult (count+1) :=
  let clipped := positiveArray input
  let total := sumArray clipped.data
  let output := if total.data.numerator.isEmpty then
      buildArray (count+1) (fun index => ⟨if index.val=0 then one else zero,3⟩)
    else normalizeArray clipped.data
  ⟨output.data,clipped.work+total.work+output.work+4⟩

theorem binaryPositiveNormalize_value {count : ℕ} (input : Vector RationalBits (count+1))
    (index : Fin (count+1)) :
    ((binaryPositiveNormalize input).data.get index).decode=
      positiveWeightProgram (fun i => (input.get i).decode) index := by
  have ht : (sumArray (positiveArray input).data).data.decode=
      positiveNormalizerProgram (fun i => (input.get i).decode) := by
    simp only [sumArray_value,positiveArray_value,positiveNormalizerProgram,positivePartProgram]
  have hz : (sumArray (positiveArray input).data).data.numerator.isEmpty=true ↔
      positiveNormalizerProgram (fun i => (input.get i).decode)=0 := by
    rw [List.isEmpty_iff,numerator_empty_iff,ht]
  unfold binaryPositiveNormalize positiveWeightProgram
  dsimp only
  split <;> rename_i hc
  · rw [if_pos (hz.mp hc)]
    simp only [buildArray_get]
    by_cases hi : index=0
    · subst index
      simp only [Fin.val_zero,ite_true,one_value]
    · have hv : index.val≠0 := fun hh => hi (Fin.ext hh)
      simp only [hi,hv,ite_false,zero_value]
  · rw [if_neg (fun hh => hc (hz.mpr hh)),normalizeArray_value]
    simp only [positiveArray_value,positivePartProgram,positiveNormalizerProgram]

theorem binaryPositiveNormalize_height {count : ℕ} (input : Vector RationalBits (count+1)) (height : ℕ)
    (hh : ∀ index,HeightBound (input.get index).decode height) (index : Fin (count+1)) :
    HeightBound ((binaryPositiveNormalize input).data.get index).decode (height+(count+1)*(height+1)) := by
  rw [binaryPositiveNormalize_value]
  exact positiveWeightProgram_height _ height hh index

def binaryPositiveNormalizeWork (count height : ℕ) : ℕ :=
  count*(3*count+9)+sumArrayWork count height+normalizeArrayWork count height+5*count+10

theorem binaryPositiveNormalize_work {count : ℕ} (input : Vector RationalBits (count+1)) (height : ℕ)
    (hh : ∀ index,HeightBound (input.get index).decode height) :
    (binaryPositiveNormalize input).work≤ binaryPositiveNormalizeWork (count+1) height := by
  have hc := positiveArray_height input height hh
  have wp := positiveArray_work input
  have wt := sumArray_work (positiveArray input).data height hc
  have wn := normalizeArray_work (positiveArray input).data height hc
  have wz := buildArray_work (count+1) 3
    (fun index => ⟨if index.val=0 then one else zero,3⟩) (fun _ => le_rfl)
  unfold binaryPositiveNormalize
  dsimp only
  split <;> unfold binaryPositiveNormalizeWork <;> nlinarith

end AFT.BinaryArithmetic.RationalBits

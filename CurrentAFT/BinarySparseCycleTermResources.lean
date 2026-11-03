import CurrentAFT.BinarySparseCycleEvaluation

/-! Bit lengths and costs of each actual sparse-cycle Gaussian summand. -/
namespace CurrentAFT.BinarySparseCycleTermResources
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinarySparseCycleEvaluation
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def rootEntryWork (edges count cutoff : ℕ) : ℕ :=
  3*count+6*edges+100*(2*cutoff+2)^2+20*(2*cutoff+1)+30

 theorem rootEntry_bounds {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) (slot : Fin count) :
    (rootEntry ranks word slot).value.digits.length ≤ 2*cutoff+2 ∧
      (rootEntry ranks word slot).work ≤ rootEntryWork edges count cutoff := by
  have hselected : (readList ranks.toList slot.val).data = some (ranks.get slot) := by
    rw [readList_value,List.getElem?_eq_getElem (by simpa only [Vector.length_toList] using slot.isLt)]
    rfl
  let first := readVector (⟨0,by omega⟩ : Fin (2*cutoff+1)) word (ranks.get slot).1
  let second := readVector (⟨0,by omega⟩ : Fin (2*cutoff+1)) word (ranks.get slot).2
  let a := CurrentPublicShiftProgram.encode (first.value.val : ℤ)
  let b := CurrentPublicShiftProgram.encode (second.value.val : ℤ)
  have ha : a.value.digits.length ≤ 2*cutoff+1 := by
    exact (CurrentPublicShiftProgram.encode_length _).trans (by
      rw [Int.natAbs_natCast];exact first.value.isLt.le)
  have hb : b.value.digits.length ≤ 2*cutoff+1 := by
    exact (CurrentPublicShiftProgram.encode_length _).trans (by
      rw [Int.natAbs_natCast];exact second.value.isLt.le)
  have hwa : a.work ≤ 50*(2*cutoff+2)^2+1 := by
    apply (CurrentPublicShiftProgram.encode_work _).trans
    rw [Int.natAbs_natCast]
    gcongr
    exact first.value.isLt.le
  have hwb : b.work ≤ 50*(2*cutoff+2)^2+1 := by
    apply (CurrentPublicShiftProgram.encode_work _).trans
    rw [Int.natAbs_natCast]
    gcongr
    exact second.value.isLt.le
  have hsub := IntegerBits.subtract_length a.value b.value
  have hwsub := IntegerBits.subtract_work a.value b.value
  have hlist := readList_work ranks.toList slot.val
  rw [Vector.length_toList] at hlist
  have hfirst := readVector_work (⟨0,by omega⟩ : Fin (2*cutoff+1)) word (ranks.get slot).1
  have hsecond := readVector_work (⟨0,by omega⟩ : Fin (2*cutoff+1)) word (ranks.get slot).2
  simp only [rootEntry,hselected]
  change (IntegerBits.subtract a.value b.value).value.digits.length ≤ _ ∧
    (readList ranks.toList slot.val).work+count+first.work+second.work+a.work+b.work+
      (IntegerBits.subtract a.value b.value).work+7 ≤ _
  change first.work ≤ _ at hfirst
  change second.work ≤ _ at hsecond
  unfold rootEntryWork
  constructor <;> omega


def rootsWork (edges count cutoff : ℕ) : ℕ := count*(rootEntryWork edges count cutoff+2)+2

 theorem roots_bounds {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) :
    (∀ slot, ((roots ranks word).value.get slot).digits.length ≤ 2*cutoff+2) ∧
      (roots ranks word).work ≤ rootsWork edges count cutoff := by
  constructor
  · intro slot
    rw [roots,storeData_get]
    exact (rootEntry_bounds ranks word slot).1
  · exact storeData_work count _ _ (fun slot => (rootEntry_bounds ranks word slot).2)


def weightEntryWork (edges cutoff : ℕ) : ℕ := 3*edges+3*(2*cutoff+1)+8

 theorem weightEntry_bounds {edges cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (word : Vector (Fin (2*cutoff+1)) edges) (height : ℕ)
    (hh : ∀ index, HeightBound (weights.get index).decode height) (edge : Fin edges) :
    HeightBound (weightEntry weights word edge).data.decode height ∧
      (weightEntry weights word edge).work ≤ weightEntryWork edges cutoff := by
  refine ⟨?_,?_⟩
  · rw [weightEntry_value]
    exact hh _
  · have hi := readVector_work (⟨0,by omega⟩ : Fin (2*cutoff+1)) word edge
    have hw := readVector_work RationalBits.zero weights (readVector (⟨0,by omega⟩ : Fin (2*cutoff+1)) word edge).value
    change (readVector _ word edge).work+(readVector _ weights _).work+2 ≤ _
    unfold weightEntryWork
    omega


def termHeight (edges gaussianHeight testHeight : ℕ) : ℕ := edges*gaussianHeight+testHeight

def termWork (edges count cutoff gaussianHeight testHeight testWork : ℕ) : ℕ :=
  rootsWork edges count cutoff+testWork+BinaryFiniteProduct.work edges gaussianHeight (weightEntryWork edges cutoff)+
    RationalBits.primitiveWorkBound (termHeight edges gaussianHeight testHeight)+4

 theorem term_bounds {edges count cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (ranks : Vector (Fin edges × Fin edges) count) (test : Vector IntegerBits count → RationalResult)
    (gh th tw : ℕ) (hg : ∀ index, HeightBound (weights.get index).decode gh)
    (ht : ∀ roots, (∀ slot, (roots.get slot).digits.length ≤ 2*cutoff+2) →
      HeightBound (test roots).data.decode th ∧ (test roots).work ≤ tw)
    (word : Vector (Fin (2*cutoff+1)) edges) :
    HeightBound (term weights ranks test word).data.decode (termHeight edges gh th) ∧
      (term weights ranks test word).work ≤ termWork edges count cutoff gh th tw := by
  have hr := roots_bounds ranks word
  have ht' := ht (roots ranks word).value hr.1
  have hw (edge : Fin edges) := weightEntry_bounds weights word gh hg edge
  have hmh := BinaryFiniteProduct.current_height edges gh (weightEntry weights word) (fun edge => (hw edge).1)
  have hmw := BinaryFiniteProduct.current_work edges gh (weightEntryWork edges cutoff) (weightEntry weights word)
    (fun edge => (hw edge).1) (fun edge => (hw edge).2)
  have hp := RationalBits.multiply_work (BinaryFiniteProduct.current edges (weightEntry weights word)).data
    (test (roots ranks word).value).data (termHeight edges gh th)
    (hmh.mono (Nat.le_add_right _ _)) (ht'.1.mono (Nat.le_add_left _ _))
  constructor
  · change HeightBound (RationalBits.multiply _ _).data.decode _
    rw [RationalBits.multiply_value]
    exact hmh.mul ht'.1
  · change (roots ranks word).work+(test (roots ranks word).value).work+(BinaryFiniteProduct.current _ _).work+
      (RationalBits.multiply _ _).work+4 ≤ _
    unfold termWork
    omega

end CurrentAFT.BinarySparseCycleTermResources

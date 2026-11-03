import CurrentAFT.BinaryTouchedCycleRanks
import CurrentAFT.BinaryTupleSum
import CurrentAFT.BinaryFiniteProduct
import CurrentAFT.BinaryGaussianAverage
import CurrentAFT.CurrentPublicShiftProgram

/-! Literal binary Gaussian evaluation on the materialized touched edges.
All selected roots read the cached rank pair, so adjacent roots share exactly
the same latent edge coordinate. The closing predecessor is retained. -/
namespace CurrentAFT.BinarySparseCycleEvaluation
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryTouchedCycle BinaryTouchedCycleBuffer BinaryTouchedCycleRanks
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def rootEntry {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) (slot : Fin count) : CountedValue IntegerBits :=
  let selected := readList ranks.toList slot.val
  match selected.data with
  | none => ⟨IntegerBits.zero,selected.work+count+4⟩
  | some pair =>
    let first := readVector (⟨0,by omega⟩ : Fin (2*cutoff+1)) word pair.1
    let second := readVector (⟨0,by omega⟩ : Fin (2*cutoff+1)) word pair.2
    let firstBits := CurrentPublicShiftProgram.encode (first.value.val : ℤ)
    let secondBits := CurrentPublicShiftProgram.encode (second.value.val : ℤ)
    let difference := IntegerBits.subtract firstBits.value secondBits.value
    ⟨difference.value,selected.work+count+first.work+second.work+firstBits.work+secondBits.work+difference.work+7⟩

 theorem rootEntry_value {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) (slot : Fin count) :
    (rootEntry ranks word slot).value.decode =
      ((word.get (ranks.get slot).1).val : ℤ) - (word.get (ranks.get slot).2).val := by
  simp only [rootEntry,readList_value]
  rw [List.getElem?_eq_getElem (by simpa only [Vector.length_toList] using slot.isLt)]
  simp only [Vector.getElem_toList,IntegerBits.subtract_value,CurrentPublicShiftProgram.encode_value,readVector_value]
  rfl


def roots {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) : CountedValue (Vector IntegerBits count) :=
  storeData count (rootEntry ranks word)

 theorem roots_value {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) (slot : Fin count) :
    ((roots ranks word).value.get slot).decode =
      ((word.get (ranks.get slot).1).val : ℤ) - (word.get (ranks.get slot).2).val := by
  rw [roots,storeData_get,rootEntry_value]


def weightEntry {edges cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (word : Vector (Fin (2*cutoff+1)) edges) (edge : Fin edges) : RationalResult :=
  let index := readVector (⟨0,by omega⟩ : Fin (2*cutoff+1)) word edge
  let weight := readVector RationalBits.zero weights index.value
  ⟨weight.value,index.work+weight.work+2⟩

 theorem weightEntry_value {edges cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (word : Vector (Fin (2*cutoff+1)) edges) (edge : Fin edges) :
    (weightEntry weights word edge).data.decode = (weights.get (word.get edge)).decode := by
  simp only [weightEntry,readVector_value]


def term {edges count cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (ranks : Vector (Fin edges × Fin edges) count) (test : Vector IntegerBits count → RationalResult)
    (word : Vector (Fin (2*cutoff+1)) edges) : RationalResult :=
  let rootWord := roots ranks word
  let response := test rootWord.value
  let mass := BinaryFiniteProduct.current edges (weightEntry weights word)
  let product := RationalBits.multiply mass.data response.data
  ⟨product.data,rootWord.work+response.work+mass.work+product.work+4⟩

 theorem term_value {edges count cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (ranks : Vector (Fin edges × Fin edges) count) (test : Vector IntegerBits count → RationalResult)
    (ideal : (Fin count → ℤ) → ℚ) (htest : ∀ rootWord, (test rootWord).data.decode = ideal (fun slot => (rootWord.get slot).decode))
    (word : Vector (Fin (2*cutoff+1)) edges) :
    (term weights ranks test word).data.decode =
      (∏ edge, (weights.get (word.get edge)).decode) *
        ideal (fun slot => ((word.get (ranks.get slot).1).val : ℤ) - (word.get (ranks.get slot).2).val) := by
  simp only [term,RationalBits.multiply_value,BinaryFiniteProduct.current_value,weightEntry_value,htest,roots_value]


def current {body count : ℕ} (security cutoff bits : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (test : Vector IntegerBits count → RationalResult) : RationalResult :=
  let touched := prepare hb sites
  let rankPairs := positions hb sites
  let weights := CurrentGaussianBits.table security cutoff bits
  let summed := BinaryTupleSum.current (2*cutoff+1) touched.value.length (term weights.data rankPairs.value test)
  ⟨summed.data,touched.work+touched.value.length+rankPairs.work+weights.work+summed.work+5⟩

 theorem current_tuple_value {body count : ℕ} (security cutoff bits : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (test : Vector IntegerBits count → RationalResult) (ideal : (Fin count → ℤ) → ℚ)
    (htest : ∀ rootWord, (test rootWord).data.decode = ideal (fun slot => (rootWord.get slot).decode)) :
    (current security cutoff bits hb sites test).data.decode =
      ∑ word : Fin (prepare hb sites).value.length → Fin (2*cutoff+1),
        (∏ edge, windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits (word edge)) *
          ideal (fun slot => ((word (((positions hb sites).value.get slot).1)).val : ℤ) -
            (word (((positions hb sites).value.get slot).2)).val) := by
  change (BinaryTupleSum.current _ _ _).data.decode = _
  rw [BinaryTupleSum.current_value]
  simp only [term_value _ _ _ ideal htest,Vector.get_ofFn,CurrentGaussianBits.table_value]

end CurrentAFT.BinarySparseCycleEvaluation

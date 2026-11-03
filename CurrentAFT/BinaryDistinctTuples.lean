import CurrentAFT.BinaryTupleSum
import CurrentAFT.BinaryProposalGuard
import CurrentAFT.CyclePatternProgram
import AFT.UnaryPolynomialCounters

/-! # Executed distinct ordered selections and their exact normalizer -/
namespace CurrentAFT.BinaryDistinctTuples
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter

def pairCheck (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) (first second : Fin count) : CountedValue Bool :=
  let ordered := lessCounter first.val second.val
  let left := readVector ⟨0, hp⟩ word first
  let right := readVector ⟨0, hp⟩ word second
  let forward := lessCounter left.value.val right.value.val
  let backward := lessCounter right.value.val left.value.val
  ⟨if ordered.value then forward.value || backward.value else true,
    ordered.work+left.work+right.work+forward.work+backward.work+4⟩

theorem pairCheck_value (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) (first second : Fin count) :
    (pairCheck pool count hp word first second).value = true ↔
      (first.val < second.val → word.get first ≠ word.get second) := by
  simp only [pairCheck, readVector_value]
  by_cases hpos : (lessCounter first.val second.val).value = true
  · rw [if_pos hpos, Bool.or_eq_true, lessCounter_value, lessCounter_value]
    have hlt := (lessCounter_value _ _).mp hpos
    constructor
    · intro h _ he
      have he' := congrArg Fin.val he
      omega
    · intro h
      have hn := h hlt
      have hn' : (word.get first).val ≠ (word.get second).val := fun he => hn (Fin.ext he)
      omega
  · rw [if_neg hpos]
    have hnot : ¬ first.val < second.val := fun h => hpos ((lessCounter_value _ _).mpr h)
    simp only [hnot, false_implies]

def current (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) : CountedValue Bool :=
  BinaryProposalGuard.allFin count (fun first =>
    BinaryProposalGuard.allFin count (fun second => pairCheck pool count hp word first second))

theorem current_value (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) :
    (current pool count hp word).value = true ↔ Function.Injective word.get := by
  simp only [current, BinaryProposalGuard.allFin_value, pairCheck_value]
  constructor
  · intro h first second he
    by_contra hn
    have hv : first.val ≠ second.val := fun hv => hn (Fin.ext hv)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · exact h first second hlt he
    · exact h second first hgt he.symm
  · intro h first second hlt he
    have hi := h he
    have hv := congrArg Fin.val hi
    omega

def pairWork (pool count : ℕ) : ℕ := 12*count+12*pool+20
def work (pool count : ℕ) : ℕ := count*(count*(pairWork pool count+2)+3)+1

theorem pairCheck_work (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) (first second : Fin count) :
    (pairCheck pool count hp word first second).work ≤ pairWork pool count := by
  have wo := lessCounter_work first.val second.val
  have wl := readVector_work (⟨0, hp⟩ : Fin pool) word first
  have wr := readVector_work (⟨0, hp⟩ : Fin pool) word second
  have wf := lessCounter_work (readVector (⟨0, hp⟩ : Fin pool) word first).value.val (readVector (⟨0, hp⟩ : Fin pool) word second).value.val
  have wb := lessCounter_work (readVector (⟨0, hp⟩ : Fin pool) word second).value.val (readVector (⟨0, hp⟩ : Fin pool) word first).value.val
  have hf := first.isLt
  have hs := second.isLt
  have hl := (readVector (⟨0, hp⟩ : Fin pool) word first).value.isLt
  have hr := (readVector (⟨0, hp⟩ : Fin pool) word second).value.isLt
  change _+_+_+_+_+4 ≤ _
  unfold pairWork
  omega

theorem current_work (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) :
    (current pool count hp word).work ≤ work pool count := by
  exact BinaryProposalGuard.allFin_work count (count*(pairWork pool count+2)+1) _
    (fun first => BinaryProposalGuard.allFin_work count (pairWork pool count) _ (fun second => pairCheck_work pool count hp word first second))

def guarded (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → RationalResult)
    (word : Vector (Fin pool) count) : RationalResult :=
  let check := current pool count hp word
  let result := kernel word
  ⟨if check.value then result.data else zero, check.work+result.work+2⟩

theorem guarded_value (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → RationalResult)
    (word : Vector (Fin pool) count) :
    (guarded pool count hp kernel word).data.decode =
      if Function.Injective word.get then (kernel word).data.decode else 0 := by
  unfold guarded
  dsimp only
  by_cases h : (current pool count hp word).value = true
  · simp only [if_pos h, if_pos ((current_value _ _ _ _).mp h)]
  · simp only [if_neg h, if_neg (fun h' => h ((current_value _ _ _ _).mpr h')), zero_value]

def sum (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → RationalResult) : RationalResult :=
  BinaryTupleSum.current pool count (guarded pool count hp kernel)

def normalizer (pool count : ℕ) (hp : 0 < pool) : RationalResult :=
  sum pool count hp (fun _ => ⟨one, 1⟩)


noncomputable section
open scoped Classical

theorem sum_value (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → RationalResult) :
    (sum pool count hp kernel).data.decode =
      ∑ selection : Fin count ↪ Fin pool, (kernel (Vector.ofFn selection)).data.decode := by
  letI : Fintype {word : Fin count → Fin pool // Function.Injective word} := Fintype.ofFinite _
  rw [sum, BinaryTupleSum.current_value]
  simp only [guarded_value, BinaryTupleSum.get_ofFn_fun]
  have hs := (Finset.sum_subtype (p := fun word : Fin count → Fin pool => Function.Injective word) (F := inferInstance)
    (Finset.univ.filter Function.Injective) (by simp) (fun word => (kernel (Vector.ofFn word)).data.decode))
  rw [Finset.sum_filter] at hs
  rw [hs]
  exact (Equiv.sum_comp (CyclePatternProgram.selectionEquiv pool count)
    (fun word => (kernel (Vector.ofFn word.val)).data.decode)).symm

theorem sum_bounds (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → RationalResult)
    (leafHeight leafWork : ℕ) (hh : ∀ word, HeightBound (kernel word).data.decode leafHeight)
    (hw : ∀ word, (kernel word).work ≤ leafWork) :
    HeightBound (sum pool count hp kernel).data.decode (BinaryTupleSum.height pool count leafHeight) ∧
      (sum pool count hp kernel).work ≤ BinaryTupleSum.work pool count leafHeight (work pool count+leafWork+2) := by
  apply BinaryTupleSum.current_bounds
  · intro word
    rw [guarded_value]
    split_ifs
    · exact hh word
    · exact HeightBound.zero.mono (Nat.zero_le _)
  · intro word
    exact Nat.add_le_add_right (Nat.add_le_add (current_work pool count hp word) (hw word)) 2


theorem normalizer_value (pool count : ℕ) (hp : 0 < pool) :
    (normalizer pool count hp).data.decode = (pool.descFactorial count:ℚ) := by
  rw [normalizer, sum_value]
  simp only [one_value, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_embedding_eq, Fintype.card_fin]

end
end CurrentAFT.BinaryDistinctTuples

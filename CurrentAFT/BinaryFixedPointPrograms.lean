import CurrentAFT.BinaryWeightedPointKernel
import CurrentAFT.FixedFamilyPrograms
import AFT.BinaryChartMetadata

/-! # One finite program list for each fixed calibration order

The list is fixed before the security parameter. Runtime dispatch scans its
stored arity tags using executed counters. Choice occurs only in the proof
that this finite collection of static encoded programs exists.
-/
namespace CurrentAFT.BinaryFixedPointPrograms
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Program (order : ℕ) (arity : TruncatedArity order) :=
  BinaryWeightedPointKernel.Program arity.val.1.val arity.val.2.val
abbrev Entry (order : ℕ) := (arity : TruncatedArity order) × Program order arity

open FixedFamilyPrograms (matchArity matchArity_value matchArity_work)

def lookup (order : ℕ) (target : TruncatedArity order) : List (Entry order) → CountedValue (Program order target)
  | [] => ⟨.literal zero, 1⟩
  | entry::tail =>
      let equal := matchArity order entry.1 target
      if h : equal.value = true then
        let same := (matchArity_value order entry.1 target).mp h
        ⟨same ▸ entry.2, equal.work+2⟩
      else
        let result := lookup order target tail
        ⟨result.value, equal.work+result.work+2⟩

theorem lookup_work (order : ℕ) (target : TruncatedArity order) (list : List (Entry order)) :
    (lookup order target list).work ≤ list.length*(12*order+7)+1 := by
  induction list with
  | nil => simp [lookup]
  | cons entry tail ih =>
    have hm := matchArity_work order entry.1 target
    simp only [lookup, List.length_cons]
    split_ifs <;> nlinarith


def current (security bits order : ℕ) (programs : List (Entry order)) (arity : TruncatedArity order)
    (sourcePrimary colors : Vector (BinaryWeightedPointKernel.Color security) arity.val.1.val)
    (sourceBody centers : Vector (BinaryWeightedPointKernel.Color security) arity.val.2.val) : RationalResult :=
  let selected := lookup order arity programs
  let value := BinaryWeightedPointKernel.current security bits selected.value sourcePrimary colors sourceBody centers
  ⟨value.data,selected.work+value.work+1⟩

noncomputable section
open scoped Classical BigOperators

def Correct (order : ℕ) (list : List (Entry order)) : Prop :=
  ∀ entry ∈ list, entry.2.meaning RationalBits.decode = BinaryWeightedPointKernel.pointSyntax entry.1.val.1.val entry.1.val.2.val

def Complete (order : ℕ) (list : List (Entry order)) : Prop :=
  ∀ arity, ∃ program : Program order arity, (⟨arity, program⟩ : Entry order) ∈ list

theorem lookup_meaning (order : ℕ) (target : TruncatedArity order) (list : List (Entry order))
    (hcorrect : Correct order list) (hcomplete : ∃ program : Program order target, (⟨target, program⟩ : Entry order) ∈ list) :
    (lookup order target list).value.meaning RationalBits.decode = BinaryWeightedPointKernel.pointSyntax target.val.1.val target.val.2.val := by
  induction list with
  | nil => simp only [List.not_mem_nil, exists_false] at hcomplete
  | cons entry tail ih =>
    rcases entry with ⟨arity, program⟩
    by_cases h : (matchArity order arity target).value = true
    · have he := (matchArity_value order arity target).mp h
      subst target
      simp only [lookup, h, dite_true]
      exact hcorrect ⟨arity, program⟩ List.mem_cons_self
    · have ht : ∃ program : Program order target, (⟨target, program⟩ : Entry order) ∈ tail := by
        obtain ⟨value, hv⟩ := hcomplete
        refine ⟨value, ?_⟩
        rcases List.mem_cons.mp hv with he | ht
        · have ha := congrArg Sigma.fst he
          exact False.elim (h ((matchArity_value order arity target).mpr ha.symm))
        · exact ht
      simp only [lookup, h]
      exact ih (fun entry he => hcorrect entry (List.mem_cons_of_mem _ he)) ht

/-- The quantified data depend on the order alone, rather than on the
security parameter or a hidden source. -/
theorem exists_complete (order : ℕ) : ∃ list : List (Entry order), Correct order list ∧ Complete order list := by
  let programs := fun arity : TruncatedArity order => Classical.choose (BinaryWeightedPointKernel.exists_stored arity.val.1.val arity.val.2.val)
  let list : List (Entry order) := (Finset.univ : Finset (TruncatedArity order)).toList.map
    (fun arity => ⟨arity, programs arity⟩)
  refine ⟨list, ?_, ?_⟩
  · intro entry hentry
    obtain ⟨arity, _, he⟩ := List.mem_map.mp hentry
    subst entry
    exact Classical.choose_spec (BinaryWeightedPointKernel.exists_stored arity.val.1.val arity.val.2.val)
  · intro arity
    refine ⟨programs arity, List.mem_map.mpr ?_⟩
    exact ⟨arity, Finset.mem_toList.mpr (Finset.mem_univ arity), rfl⟩


theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (arity : TruncatedArity order)
    (sourcePrimary colors : Vector (BinaryWeightedPointKernel.Color security) arity.val.1.val)
    (sourceBody centers : Vector (BinaryWeightedPointKernel.Color security) arity.val.2.val) :
    (current security bits order programs arity sourcePrimary colors sourceBody centers).data.decode=
      WeightedPointKernelProgram.current security bits arity.val.1.val arity.val.2.val
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val)
        (fun index => (colors.get index).val) (fun index => (centers.get index).val) :=
  BinaryWeightedPointKernel.current_value security bits (lookup order arity programs).value
    (lookup_meaning order arity programs hcorrect (hcomplete arity)) sourcePrimary colors sourceBody centers

noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  ∑ arity : TruncatedArity order, BinaryWeightedPointKernel.heightPolynomial (lookup order arity programs).value precision
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (programs.length*(12*order+7)+2)+∑ arity : TruncatedArity order,
    BinaryWeightedPointKernel.workPolynomial (lookup order arity programs).value precision

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ)
    (arity : TruncatedArity order)
    (sourcePrimary colors : Vector (BinaryWeightedPointKernel.Color security) arity.val.1.val)
    (sourceBody centers : Vector (BinaryWeightedPointKernel.Color security) arity.val.2.val) :
    HeightBound (current security (precision.eval security) order programs arity sourcePrimary colors sourceBody centers).data.decode
      ((heightPolynomial order programs precision).eval security) ∧
      (current security (precision.eval security) order programs arity sourcePrimary colors sourceBody centers).work ≤
        (workPolynomial order programs precision).eval security := by
  have h := BinaryWeightedPointKernel.current_bounds security precision (lookup order arity programs).value sourcePrimary colors sourceBody centers
  have wh := lookup_work order arity programs
  constructor
  · apply h.1.mono
    rw [heightPolynomial,Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (f := fun arity : TruncatedArity order =>
      (BinaryWeightedPointKernel.heightPolynomial (lookup order arity programs).value precision).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ arity)
  · have hs : (BinaryWeightedPointKernel.workPolynomial (lookup order arity programs).value precision).eval security ≤
        ∑ arity : TruncatedArity order, (BinaryWeightedPointKernel.workPolynomial (lookup order arity programs).value precision).eval security :=
      Finset.single_le_sum (f := fun arity : TruncatedArity order =>
        (BinaryWeightedPointKernel.workPolynomial (lookup order arity programs).value precision).eval security)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ arity)
    change _+_+1 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_finset_sum]
    omega

end
end CurrentAFT.BinaryFixedPointPrograms

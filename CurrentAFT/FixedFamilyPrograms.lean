import CurrentAFT.BinaryFamilyProduct
import AFT.BinaryChartMetadata

/-! # One finite program list for each fixed calibration order

The list is fixed before the security parameter. Runtime dispatch scans its
stored arity tags using executed counters. Choice occurs only in the proof
that this finite collection of static encoded programs exists.
-/
namespace CurrentAFT.FixedFamilyPrograms
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Program (order : ℕ) (arity : TruncatedArity order) :=
  StoredScalarProgram (FamilyProductSyntax.Leaf order arity) RationalBits
abbrev Entry (order : ℕ) := (arity : TruncatedArity order) × Program order arity

def matchArity (order : ℕ) (first second : TruncatedArity order) : CountedValue Bool :=
  let primary := equalCounter first.val.1.val second.val.1.val
  let body := equalCounter first.val.2.val second.val.2.val
  ⟨primary.value && body.value, primary.work+body.work+1⟩

theorem matchArity_value (order : ℕ) (first second : TruncatedArity order) :
    (matchArity order first second).value = true ↔ first = second := by
  simp only [matchArity, Bool.and_eq_true, equalCounter_value]
  constructor
  · intro h
    exact Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  · intro h
    subst second
    exact ⟨rfl, rfl⟩

theorem matchArity_work (order : ℕ) (first second : TruncatedArity order) :
    (matchArity order first second).work ≤ 12*order+5 := by
  have hp := equalCounter_work first.val.1.val second.val.1.val
  have hb := equalCounter_work first.val.2.val second.val.2.val
  have hf := first.property
  have hs := second.property
  change (equalCounter first.val.1.val second.val.1.val).work +
    (equalCounter first.val.2.val second.val.2.val).work + 1 ≤ _
  omega

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

def nodes {order : ℕ} : List (Entry order) → ℕ
  | [] => 1
  | entry::tail => max (entry.2.meaning RationalBits.decode).nodes (nodes tail)

def literals {order : ℕ} : List (Entry order) → ℕ
  | [] => rationalLiteralHeight zero.decode
  | entry::tail => max (BinaryFixedScalarProgram.literalBound (entry.2.meaning RationalBits.decode)) (literals tail)

theorem lookup_bounds (order : ℕ) (target : TruncatedArity order) (list : List (Entry order)) :
    ((lookup order target list).value.meaning RationalBits.decode).nodes ≤ nodes list ∧
      BinaryFixedScalarProgram.literalBound ((lookup order target list).value.meaning RationalBits.decode) ≤ literals list := by
  induction list with
  | nil => exact ⟨le_refl _, le_refl _⟩
  | cons entry tail ih =>
    rcases entry with ⟨arity, program⟩
    by_cases h : (matchArity order arity target).value = true
    · have he := (matchArity_value order arity target).mp h
      subst target
      simp only [lookup, h, dite_true, nodes, literals]
      exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩
    · simp only [lookup, h, nodes, literals]
      exact ⟨ih.1.trans (Nat.le_max_right _ _), ih.2.trans (Nat.le_max_right _ _)⟩

noncomputable section
open scoped Classical

def Correct (order : ℕ) (list : List (Entry order)) : Prop :=
  ∀ entry ∈ list, entry.2.meaning RationalBits.decode = FamilyProductSyntax.product order entry.1

def Complete (order : ℕ) (list : List (Entry order)) : Prop :=
  ∀ arity, ∃ program : Program order arity, (⟨arity, program⟩ : Entry order) ∈ list

theorem lookup_meaning (order : ℕ) (target : TruncatedArity order) (list : List (Entry order))
    (hcorrect : Correct order list) (hcomplete : ∃ program : Program order target, (⟨target, program⟩ : Entry order) ∈ list) :
    (lookup order target list).value.meaning RationalBits.decode = FamilyProductSyntax.product order target := by
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
  let programs := fun arity : TruncatedArity order => Classical.choose (FamilyProductSyntax.exists_stored order arity)
  let list : List (Entry order) := (Finset.univ : Finset (TruncatedArity order)).toList.map
    (fun arity => ⟨arity, programs arity⟩)
  refine ⟨list, ?_, ?_⟩
  · intro entry hentry
    obtain ⟨arity, _, he⟩ := List.mem_map.mp hentry
    subst entry
    exact Classical.choose_spec (FamilyProductSyntax.exists_stored order arity)
  · intro arity
    refine ⟨programs arity, List.mem_map.mpr ?_⟩
    exact ⟨arity, Finset.mem_toList.mpr (Finset.mem_univ arity), rfl⟩

end
end CurrentAFT.FixedFamilyPrograms

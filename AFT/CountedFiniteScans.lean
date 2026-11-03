import AFT.CountedDependentArray

/-! # Counted finite scans

The loops inspect each entry once. Filtering preserves the input order and
its no-duplicate certificate, so forming the resulting finite set performs
no duplicate-removal or sorting pass.
-/
namespace AFT.RationalRejectionProgram
open scoped BigOperators

def countedListFilter {State : Type*} (test : State → CountedValue Bool) :
    List State → CountedValue (List State)
  | [] => ⟨[],0⟩
  | first::rest =>
      let selected := test first
      let remaining := countedListFilter test rest
      ⟨if selected.value then first::remaining.value else remaining.value,
        selected.work+remaining.work+2⟩

theorem countedListFilter_value {State : Type*} (test : State → CountedValue Bool)
    (input : List State) :
    (countedListFilter test input).value=input.filter (fun entry => (test entry).value) := by
  induction input with
  | nil => rfl
  | cons first rest ih => simp only [countedListFilter,List.filter_cons,ih]

theorem countedListFilter_work {State : Type*} (test : State → CountedValue Bool)
    (input : List State) (bound : ℕ) (htest : ∀ entry∈input,(test entry).work≤ bound) :
    (countedListFilter test input).work≤ input.length*(bound+2) := by
  induction input with
  | nil => simp [countedListFilter]
  | cons first rest ih =>
      have hh := htest first (by simp)
      have hr := ih (fun entry he => htest entry (by simp [he]))
      simp only [countedListFilter,List.length_cons]
      nlinarith

def countedFinFilter (count : ℕ) (test : Fin count → CountedValue Bool) :
    CountedValue (Finset (Fin count)) :=
  let result := countedListFilter test (List.ofFn id)
  ⟨⟨result.value,by
      rw [countedListFilter_value]
      exact List.Nodup.filter _ (List.nodup_ofFn.mpr Function.injective_id)⟩,
    result.work+count⟩

theorem countedFinFilter_value (count : ℕ) (test : Fin count → CountedValue Bool) :
    (countedFinFilter count test).value=Finset.univ.filter (fun index => (test index).value) := by
  ext index
  simp [countedFinFilter,countedListFilter_value]

theorem countedFinFilter_work (count : ℕ) (test : Fin count → CountedValue Bool)
    (bound : ℕ) (htest : ∀ index,(test index).work≤ bound) :
    (countedFinFilter count test).work≤ count*(bound+3) := by
  have hh := countedListFilter_work test (List.ofFn id) bound (fun index _ => htest index)
  simp only [List.length_ofFn] at hh
  unfold countedFinFilter
  dsimp only
  nlinarith

def countedListAll {State : Type*} (test : State → CountedValue Bool) :
    List State → CountedValue Bool
  | [] => ⟨true,0⟩
  | first::rest =>
      let selected := test first
      let remaining := countedListAll test rest
      ⟨selected.value && remaining.value,selected.work+remaining.work+1⟩

theorem countedListAll_value {State : Type*} (test : State → CountedValue Bool)
    (input : List State) :
    (countedListAll test input).value=true ↔ ∀ entry∈input,(test entry).value=true := by
  induction input with
  | nil => simp [countedListAll]
  | cons first rest ih => simp [countedListAll,ih]

theorem countedListAll_work {State : Type*} (test : State → CountedValue Bool)
    (input : List State) (bound : ℕ) (htest : ∀ entry∈input,(test entry).work≤ bound) :
    (countedListAll test input).work≤ input.length*(bound+1) := by
  induction input with
  | nil => simp [countedListAll]
  | cons first rest ih =>
      have hh := htest first (by simp)
      have hr := ih (fun entry he => htest entry (by simp [he]))
      simp only [countedListAll,List.length_cons]
      nlinarith

def countedFinAll (count : ℕ) (test : Fin count → CountedValue Bool) : CountedValue Bool :=
  let result := countedListAll test (List.ofFn id)
  ⟨result.value,result.work+count⟩

theorem countedFinAll_value (count : ℕ) (test : Fin count → CountedValue Bool) :
    (countedFinAll count test).value=true ↔ ∀ index,(test index).value=true := by
  simp [countedFinAll,countedListAll_value]

theorem countedFinAll_work (count : ℕ) (test : Fin count → CountedValue Bool)
    (bound : ℕ) (htest : ∀ index,(test index).work≤ bound) :
    (countedFinAll count test).work≤ count*(bound+2) := by
  have hh := countedListAll_work test (List.ofFn id) bound (fun index _ => htest index)
  simp only [List.length_ofFn] at hh
  unfold countedFinAll
  dsimp only
  nlinarith

end AFT.RationalRejectionProgram

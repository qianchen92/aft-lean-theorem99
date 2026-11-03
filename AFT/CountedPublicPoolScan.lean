import AFT.PublicPoolScanProgram

/-! # Literal finite-range generation and public pool query costs -/
namespace AFT.PublicPoolProgram

structure RangeResult (population : ℕ) where
  values : List (Fin population)
  work : ℕ

/-- An intentionally elementary range generator. Appending the next index
is charged the entire current list length. -/
def rangePrefix (population : ℕ) : (length : ℕ) → length ≤ population → RangeResult population
  | 0, _ => ⟨[],0⟩
  | length+1, h =>
      let previous := rangePrefix population length (by omega)
      ⟨previous.values ++ [⟨length,by omega⟩], previous.work+previous.values.length+2⟩

theorem rangePrefix_values (population length : ℕ) (h : length ≤ population) :
    (rangePrefix population length h).values.map Fin.val = List.range length := by
  induction length with
  | zero => rfl
  | succ length ih => simp only [rangePrefix, List.map_append, List.map_cons, List.map_nil, ih, List.range_succ]

theorem rangePrefix_length (population length : ℕ) (h : length ≤ population) :
    (rangePrefix population length h).values.length = length := by
  have hh := congrArg List.length (rangePrefix_values population length h)
  simpa only [List.length_map, List.length_range] using hh

theorem rangePrefix_work (population length : ℕ) (h : length ≤ population) :
    (rangePrefix population length h).work ≤ (length+1)^2 := by
  induction length with
  | zero => simp [rangePrefix]
  | succ length ih =>
      have hh := ih (by omega : length ≤ population)
      simp only [rangePrefix, rangePrefix_length]
      nlinarith

theorem rangePrefix_full (population : ℕ) :
    (rangePrefix population population le_rfl).values = List.finRange population := by
  apply Fin.val_injective.list_map
  rw [rangePrefix_values, List.map_coe_finRange_eq_range]

/-- No implicit enumeration is charged as one operation: this function
first constructs every arithmetic coordinate and then performs the scan. -/
def runScan {population : ℕ} (legs queue : ℕ) (query : Fin population → IndexQuery population) :
    ScanResult population :=
  let range := rangePrefix population population le_rfl
  let result := scan legs queue query range.values
  ⟨result.controls,result.available,range.work+result.work⟩

theorem runScan_controls {population : ℕ} (legs queue : ℕ)
    (query : Fin population → IndexQuery population) :
    (runScan legs queue query).controls = (scan legs queue query (List.finRange population)).controls := by
  simp only [runScan,rangePrefix_full]

theorem runScan_available {population : ℕ} (legs queue : ℕ)
    (query : Fin population → IndexQuery population) :
    (runScan legs queue query).available = (scan legs queue query (List.finRange population)).available := by
  simp only [runScan,rangePrefix_full]

theorem runScan_work {population : ℕ} (legs queue : ℕ)
    (query : Fin population → IndexQuery population) (queryWork : ℕ)
    (hwork : ∀ point,(query point).work ≤ queryWork) :
    (runScan legs queue query).work ≤ (population+1)^2+population*(queryWork+5) := by
  have hr := rangePrefix_work population population le_rfl
  have hs := scan_work legs queue query (rangePrefix population population le_rfl).values queryWork hwork
  rw [rangePrefix_length] at hs
  exact Nat.add_le_add hr hs

structure ListRead (Value : Type*) where
  value : Option Value
  work : ℕ

def readList {Value : Type*} : List Value → ℕ → ListRead Value
  | [], _ => ⟨none,1⟩
  | value::_, 0 => ⟨some value,1⟩
  | _::remaining, index+1 =>
      let previous := readList remaining index
      ⟨previous.value,previous.work+1⟩

theorem readList_value {Value : Type*} (values : List Value) (index : ℕ) :
    (readList values index).value = values[index]? := by
  induction values generalizing index with
  | nil => simp [readList]
  | cons value values ih => cases index <;> simp [readList,ih]

theorem readList_work {Value : Type*} (values : List Value) (index : ℕ) :
    (readList values index).work ≤ values.length+1 := by
  induction values generalizing index with
  | nil => simp [readList]
  | cons value values ih =>
      cases index with
      | zero => simp [readList]
      | succ index =>
          have hh := ih index
          simp only [readList,List.length_cons]
          omega

structure ValueQuery (Value : Type*) where
  value : Value
  work : ℕ

/-- A complete pair accessor. The body branch uses the suffix of the
available list after the matched compensator prefix. -/
def readPair {population : ℕ} {Color : Type*} (pools : ScanResult population)
    (marks centers : Fin population → ValueQuery Color) (primary : Bool) (index : ℕ) :
    ListRead (Color × Color) :=
  if primary then
    let first := readList pools.controls index
    let second := readList pools.available index
    match first.value,second.value with
    | some mark,some center =>
        let marked := marks mark
        let centered := centers center
        ⟨some (marked.value,centered.value),first.work+second.work+marked.work+centered.work+4⟩
    | _,_ => ⟨none,first.work+second.work+4⟩
  else
    let selected := readList pools.available (pools.controls.length+index)
    match selected.value with
    | some center =>
        let marked := marks center
        let centered := centers center
        ⟨some (marked.value,centered.value),pools.controls.length+selected.work+marked.work+centered.work+4⟩
    | none => ⟨none,pools.controls.length+selected.work+4⟩

theorem readPair_work {population : ℕ} {Color : Type*} (pools : ScanResult population)
    (marks centers : Fin population → ValueQuery Color) (primary : Bool) (index queryWork : ℕ)
    (hcontrols : pools.controls.length ≤ population) (havailable : pools.available.length ≤ population)
    (hmarks : ∀ point,(marks point).work ≤ queryWork)
    (hcenters : ∀ point,(centers point).work ≤ queryWork) :
    (readPair pools marks centers primary index).work ≤ 2*population+2*queryWork+6 := by
  have hc := readList_work pools.controls index
  have ha := readList_work pools.available index
  have hs := readList_work pools.available (pools.controls.length+index)
  unfold readPair
  split
  · dsimp only
    split <;> simp only
    · rename_i mark center _ _
      have hm := hmarks mark
      have hh := hcenters center
      omega
    · omega
  · dsimp only
    split <;> simp only
    · rename_i center _
      have hm := hmarks center
      have hh := hcenters center
      omega
    · omega

end AFT.PublicPoolProgram

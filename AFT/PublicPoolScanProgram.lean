import AFT.PublicPoolProgram

/-! # Scanning public pool lists, with explicit query and loop counters -/
namespace AFT.PublicPoolProgram

theorem matchingSet_eq_take (population legs queue : ℕ)
    (placement : Equiv.Perm (Fin population))
    (hsize : (controlSet population legs queue placement).card ≤
      (availableSet population legs queue placement).card) :
    matchingSet population legs queue placement hsize =
      ((finiteSetScan (availableSet population legs queue placement)).take
        (controlSet population legs queue placement).card).toFinset := by
  let first := controlSet population legs queue placement
  let second := availableSet population legs queue placement
  ext point
  rw [List.mem_toFinset, finiteSetScan_eq_sort]
  constructor
  · intro hp
    obtain ⟨source,_,rfl⟩ := Finset.mem_map.mp hp
    have hmem : (matching population legs queue placement hsize source).val ∈ second.sort :=
      (Finset.mem_sort (α := Fin population) (· ≤ ·)).mpr (matching population legs queue placement hsize source).property
    change (matching population legs queue placement hsize source).val ∈ second.sort.take first.card
    rw [List.mem_take_iff_idxOf_lt hmem]
    have hidx : second.sort.idxOf (matching population legs queue placement hsize source).val =
        ((finiteSetNumbering (Equiv.refl _) second).symm (matching population legs queue placement hsize source)).val := by
      rw [finiteSetNumbering_refl]
      exact (Finset.orderIsoOfFin_symm_apply second rfl (matching population legs queue placement hsize source)).symm
    rw [hidx]
    simp [matching,finiteSetMatching,first,second]
  · intro hp
    have hmem : point ∈ second := by simpa using (List.mem_of_mem_take hp)
    have hpos : second.sort.idxOf point < first.card :=
      (List.mem_take_iff_idxOf_lt (by simpa using hmem)).mp hp
    let position : Fin first.card := ⟨second.sort.idxOf point,hpos⟩
    apply Finset.mem_map.mpr
    refine ⟨finiteSetNumbering (Equiv.refl _) first position,Finset.mem_univ _,?_⟩
    change (finiteSetMatching (Equiv.refl _) first second hsize
      (finiteSetNumbering (Equiv.refl _) first position)).val = point
    rw [finiteSetMatching_numbering]
    have hi : Fin.castLE hsize position = (finiteSetNumbering (Equiv.refl _) second).symm ⟨point,hmem⟩ := by
      apply Fin.ext
      change second.sort.idxOf point = ((finiteSetNumbering (Equiv.refl _) second).symm ⟨point,hmem⟩).val
      rw [finiteSetNumbering_refl]
      exact (Finset.orderIsoOfFin_symm_apply second rfl ⟨point,hmem⟩).symm
    rw [hi, Equiv.apply_symm_apply]

theorem reserveScan_eq_drop (population legs queue : ℕ)
    (placement : Equiv.Perm (Fin population))
    (hsize : (controlSet population legs queue placement).card ≤
      (availableSet population legs queue placement).card) :
    finiteSetScan (reserveSet population legs queue placement hsize) =
      (finiteSetScan (availableSet population legs queue placement)).drop
        (controlSet population legs queue placement).card := by
  rw [finiteSetScan_eq_sort, finiteSetScan_eq_sort]
  apply (reserveSet population legs queue placement hsize).sortedLT_sort.eq_of_mem_iff
    (((availableSet population legs queue placement).sortedLT_sort.pairwise.sublist (List.drop_sublist _ _)).sortedLT)
  intro point
  rw [Finset.mem_sort, reserveSet, Finset.mem_sdiff, matchingSet_eq_take,
    List.mem_toFinset, finiteSetScan_eq_sort]
  let values := (availableSet population legs queue placement).sort
  have hn : values.Nodup := (availableSet population legs queue placement).sortedLT_sort.nodup
  have hd := List.disjoint_take_drop (m := (controlSet population legs queue placement).card)
    hn (le_refl _)
  constructor
  · rintro ⟨hmem,hnot⟩
    have hm : point ∈ values := by simpa [values] using hmem
    have hh : point ∈ values.take (controlSet population legs queue placement).card ∨
        point ∈ values.drop (controlSet population legs queue placement).card := by
      rw [←List.mem_append, List.take_append_drop]
      exact hm
    exact hh.resolve_left hnot
  · intro hp
    exact ⟨by simpa using (List.mem_of_mem_drop hp),
      fun ht => List.disjoint_left.mp hd ht hp⟩

structure IndexQuery (population : ℕ) where
  value : Fin population
  work : ℕ

structure ScanResult (population : ℕ) where
  controls : List (Fin population)
  available : List (Fin population)
  work : ℕ

/-- One permutation query and two comparisons per coordinate, with a
constant allowance for list construction and branching. -/
def scan {population : ℕ} (legs queue : ℕ) (query : Fin population → IndexQuery population) :
    List (Fin population) → ScanResult population
  | [] => ⟨[],[],0⟩
  | point::remaining =>
      let previous := scan legs queue query remaining
      let checked := query point
      let active := decide (queue ≤ checked.value.val)
      ⟨if active && decide (point.val < legs) then point::previous.controls else previous.controls,
       if active && decide (legs ≤ point.val) then point::previous.available else previous.available,
       previous.work + checked.work + 5⟩

theorem scan_controls {population : ℕ} (legs queue : ℕ)
    (query : Fin population → IndexQuery population) (values : List (Fin population)) :
    (scan legs queue query values).controls =
      values.filter (fun point => decide (point.val < legs ∧ queue ≤ (query point).value.val)) := by
  induction values with
  | nil => rfl
  | cons point values ih =>
      simp only [scan, ih, List.filter_cons]
      by_cases hq : queue ≤ (query point).value.val <;>
        by_cases hl : point.val < legs <;> simp [hq,hl]

theorem scan_available {population : ℕ} (legs queue : ℕ)
    (query : Fin population → IndexQuery population) (values : List (Fin population)) :
    (scan legs queue query values).available =
      values.filter (fun point => decide (legs ≤ point.val ∧ queue ≤ (query point).value.val)) := by
  induction values with
  | nil => rfl
  | cons point values ih =>
      simp only [scan, ih, List.filter_cons]
      by_cases hq : queue ≤ (query point).value.val <;>
        by_cases hl : legs ≤ point.val <;> simp [hq,hl]

theorem scan_work {population : ℕ} (legs queue : ℕ)
    (query : Fin population → IndexQuery population) (values : List (Fin population))
    (queryWork : ℕ) (hwork : ∀ point, (query point).work ≤ queryWork) :
    (scan legs queue query values).work ≤ values.length*(queryWork+5) := by
  induction values with
  | nil => simp [scan]
  | cons point values ih =>
      have hh := hwork point
      simp only [scan, List.length_cons]
      nlinarith

theorem scan_controls_correct {population : ℕ} (legs queue : ℕ)
    (query : Fin population → IndexQuery population) (placement : Equiv.Perm (Fin population))
    (hquery : ∀ point, (query point).value = placement point) :
    (scan legs queue query (List.finRange population)).controls =
      finiteSetScan (controlSet population legs queue placement) := by
  simp only [scan_controls, hquery, finiteSetScan, controlSet, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem scan_available_correct {population : ℕ} (legs queue : ℕ)
    (query : Fin population → IndexQuery population) (placement : Equiv.Perm (Fin population))
    (hquery : ∀ point, (query point).value = placement point) :
    (scan legs queue query (List.finRange population)).available =
      finiteSetScan (availableSet population legs queue placement) := by
  simp only [scan_available, hquery, finiteSetScan, availableSet, Finset.mem_filter,
    Finset.mem_univ, true_and]

end AFT.PublicPoolProgram

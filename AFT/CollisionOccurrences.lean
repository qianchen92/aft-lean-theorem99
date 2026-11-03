import AFT.CollisionCounting

/-! # First, last and middle occurrences in actual finite collision graphs -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

variable {Copy Label : Type*} [Fintype Copy] [LinearOrder Copy] [Fintype Label]

def occurrenceCopies (scope : Copy → Finset Label) (label : Label) : Finset Copy :=
  Finset.univ.filter fun copy => label ∈ scope copy

def middleScopes (scope : Copy → Finset Label) (copy : Copy) : Finset Label :=
  (scope copy).filter fun label =>
    (∃ before, before < copy ∧ label ∈ scope before) ∧
    (∃ after, copy < after ∧ label ∈ scope after)

def scopeUnion (scope : Copy → Finset Label) : Finset Label :=
  Finset.univ.biUnion scope

def NoSingletonScopes (scope : Copy → Finset Label) : Prop :=
  ∀ copy label, label ∈ scope copy → ∃ other, other ≠ copy ∧ label ∈ scope other

omit [LinearOrder Copy] in
theorem scope_card_double_count (scope : Copy → Finset Label) :
    (∑ copy, (scope copy).card) = ∑ label, (occurrenceCopies scope label).card := by
  have hcount (copy : Copy) : (scope copy).card = ∑ label : Label, if label ∈ scope copy then 1 else 0 := by
    simp
  simp_rw [hcount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro label _
  simp only [occurrenceCopies, Finset.card_filter]

omit [Fintype Label] in
theorem middleCopies_erase (scope : Copy → Finset Label) (label : Label)
    (hne : (occurrenceCopies scope label).Nonempty) :
    occurrenceCopies (middleScopes scope) label =
      ((occurrenceCopies scope label).erase ((occurrenceCopies scope label).min' hne)).erase
        ((occurrenceCopies scope label).max' hne) := by
  ext copy
  simp only [occurrenceCopies, middleScopes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨hmem, ⟨before, hbefore, hbeforeMem⟩, ⟨after, hafter, hafterMem⟩⟩
    have hmin := Finset.min'_le (occurrenceCopies scope label) before
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbeforeMem⟩)
    have hmax := Finset.le_max' (occurrenceCopies scope label) after
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hafterMem⟩)
    exact ⟨ne_of_lt (hafter.trans_le hmax), ne_of_gt (hmin.trans_lt hbefore), hmem⟩
  · rintro ⟨hmax, hmin, hmem⟩
    have hcopy : copy ∈ occurrenceCopies scope label := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
    have hminle := Finset.min'_le (occurrenceCopies scope label) copy hcopy
    have hmaxle := Finset.le_max' (occurrenceCopies scope label) copy hcopy
    refine ⟨hmem, ?_, ?_⟩
    · exact ⟨_, lt_of_le_of_ne hminle (Ne.symm hmin), (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2⟩
    · exact ⟨_, lt_of_le_of_ne hmaxle hmax, (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2⟩

omit [LinearOrder Copy] [Fintype Label] in
theorem noSingleton_occurrence_card (scope : Copy → Finset Label) (hscope : NoSingletonScopes scope)
    (label : Label) (hlabel : label ∈ scopeUnion scope) : 2 ≤ (occurrenceCopies scope label).card := by
  obtain ⟨copy, _, hcopy⟩ := Finset.mem_biUnion.mp hlabel
  obtain ⟨other, hother, hmem⟩ := hscope copy label hcopy
  apply Finset.one_lt_card.mpr
  exact ⟨copy, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcopy⟩,
    other, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, Ne.symm hother⟩

omit [Fintype Label] in
theorem middleCopies_card (scope : Copy → Finset Label) (hscope : NoSingletonScopes scope)
    (label : Label) (hlabel : label ∈ scopeUnion scope) :
    (occurrenceCopies (middleScopes scope) label).card + 2 = (occurrenceCopies scope label).card := by
  have htwo := noSingleton_occurrence_card scope hscope label hlabel
  have hne : (occurrenceCopies scope label).Nonempty := Finset.card_pos.mp (by omega)
  have hmin := Finset.min'_mem (occurrenceCopies scope label) hne
  have hmax := Finset.max'_mem (occurrenceCopies scope label) hne
  obtain ⟨first, hfirst, second, hsecond, hdiff⟩ := Finset.one_lt_card.mp htwo
  have hlt := Finset.min'_lt_max' (occurrenceCopies scope label) hfirst hsecond hdiff
  rw [middleCopies_erase scope label hne,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne_of_gt hlt, hmax⟩),
    Finset.card_erase_of_mem hmin]
  omega

omit [LinearOrder Copy] in
theorem sum_occurrenceCards (scope : Copy → Finset Label) :
    (∑ label ∈ scopeUnion scope, (occurrenceCopies scope label).card) = ∑ copy, (scope copy).card := by
  rw [scope_card_double_count]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro label _ hnot
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro copy hcopy
  exact hnot (Finset.mem_biUnion.mpr ⟨copy, Finset.mem_univ _, (Finset.mem_filter.mp hcopy).2⟩)

/-- Precisely two occurrences per used sample label remain integrated;
every other occurrence contributes a fixed-fiber penalty. -/
theorem middle_occurrence_count (scope : Copy → Finset Label) (hscope : NoSingletonScopes scope) :
    (∑ copy, (middleScopes scope copy).card) + 2 * (scopeUnion scope).card =
      ∑ copy, (scope copy).card := by
  have hmiddle : (∑ label ∈ scopeUnion scope, (occurrenceCopies (middleScopes scope) label).card) =
      ∑ copy, (middleScopes scope copy).card := by
    rw [scope_card_double_count]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro label _ hnot
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro copy hcopy
    have hm := (Finset.mem_filter.mp hcopy).2
    exact hnot (Finset.mem_biUnion.mpr ⟨copy, Finset.mem_univ _, (Finset.mem_filter.mp hm).1⟩)
  have hh := Finset.sum_congr rfl (fun label hlabel => middleCopies_card scope hscope label hlabel)
  rw [Finset.sum_add_distrib, hmiddle, sum_occurrenceCards] at hh
  simpa only [Finset.sum_const, smul_eq_mul, mul_comm] using hh

end

end AFT.CanonicalMoments

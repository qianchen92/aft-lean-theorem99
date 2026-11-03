import AFT.CollisionOccurrences

/-! # Separate collision budgets for two unequal sample pools -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

section Counting

variable {Copy PrimarySlot BodySlot PrimaryPool BodyPool : Type*}
  [Fintype Copy] [Fintype PrimarySlot] [Fintype BodySlot] [Fintype PrimaryPool] [Fintype BodyPool]

/-- Separate injective placements retain their separate exact support sizes. -/
abbrev TwoPoolPatterns (primaryUsed bodyUsed : ℕ) :=
  PatternsWithLabels (Slot := PrimarySlot) (Pool := PrimaryPool) (Copy := Copy) primaryUsed ×
    PatternsWithLabels (Slot := BodySlot) (Pool := BodyPool) (Copy := Copy) bodyUsed

theorem twoPoolPatterns_card_le (primaryUsed bodyUsed : ℕ) :
    Fintype.card (TwoPoolPatterns (Copy := Copy) (PrimarySlot := PrimarySlot) (BodySlot := BodySlot)
      (PrimaryPool := PrimaryPool) (BodyPool := BodyPool) primaryUsed bodyUsed) ≤
      ((Fintype.card PrimaryPool).descFactorial primaryUsed *
        (Fintype.card Copy * Fintype.card PrimarySlot) ^ (Fintype.card Copy * Fintype.card PrimarySlot)) *
      ((Fintype.card BodyPool).descFactorial bodyUsed *
        (Fintype.card Copy * Fintype.card BodySlot) ^ (Fintype.card Copy * Fintype.card BodySlot)) := by
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul (patternsWithLabels_card_le_uniform primaryUsed)
    (patternsWithLabels_card_le_uniform bodyUsed)

end Counting

/-- The normalization cancels each population separately, including unequal
pool sizes and the possibility that one kernel order is zero. -/
theorem twoPool_collision_normalizer_bound (primaryPopulation bodyPopulation primaryOrder bodyOrder power primaryUsed bodyUsed : ℕ)
    (hprimary : 0 < primaryPopulation) (hbody : 0 < bodyPopulation)
    (hprimaryLarge : 2 * primaryOrder ≤ primaryPopulation) (hbodyLarge : 2 * bodyOrder ≤ bodyPopulation)
    (hprimaryUsed : primaryUsed ≤ power * primaryOrder) (hbodyUsed : bodyUsed ≤ power * bodyOrder) :
    ((primaryPopulation.descFactorial primaryUsed : ℝ) * (primaryPopulation : ℝ) ^ (power * primaryOrder - primaryUsed) *
      ((bodyPopulation.descFactorial bodyUsed : ℝ) * (bodyPopulation : ℝ) ^ (power * bodyOrder - bodyUsed))) /
      (((primaryPopulation.descFactorial primaryOrder : ℝ) * (bodyPopulation.descFactorial bodyOrder : ℝ)) ^ power) ≤
      (2 : ℝ) ^ (power * (primaryOrder + bodyOrder)) := by
  have hp := collision_normalizer_bound primaryPopulation primaryOrder power primaryUsed hprimary hprimaryLarge hprimaryUsed
  have hb := collision_normalizer_bound bodyPopulation bodyOrder power bodyUsed hbody hbodyLarge hbodyUsed
  have hmul := mul_le_mul hp hb (by positivity) (by positivity)
  rw [div_mul_div_comm, ← mul_pow, ← pow_add, ← Nat.mul_add] at hmul
  exact hmul

section Occurrences

variable {Copy Label : Type*} [Fintype Copy] [LinearOrder Copy] [Fintype Label]

def roleScopes (scope : Copy → Finset Label) (role : Finset Label) (copy : Copy) : Finset Label :=
  scope copy ∩ role

omit [Fintype Copy] [LinearOrder Copy] [Fintype Label] in
theorem roleScopes_noSingleton (scope : Copy → Finset Label) (hscope : NoSingletonScopes scope)
    (role : Finset Label) : NoSingletonScopes (roleScopes scope role) := by
  intro copy label hlabel
  obtain ⟨other, hother, hmem⟩ := hscope copy label (Finset.mem_inter.mp hlabel).1
  exact ⟨other, hother, Finset.mem_inter.mpr ⟨hmem, (Finset.mem_inter.mp hlabel).2⟩⟩

omit [Fintype Label] in
theorem middle_roleScopes (scope : Copy → Finset Label) (role : Finset Label) (copy : Copy) :
    middleScopes (roleScopes scope role) copy = middleScopes scope copy ∩ role := by
  ext label
  simp only [middleScopes, roleScopes, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hmem, hrole⟩, ⟨before, hb, hbefore, _⟩, ⟨after, ha, hafter, _⟩⟩
    exact ⟨⟨hmem, ⟨before, hb, hbefore⟩, ⟨after, ha, hafter⟩⟩, hrole⟩
  · rintro ⟨⟨hmem, ⟨before, hb, hbefore⟩, ⟨after, ha, hafter⟩⟩, hrole⟩
    exact ⟨⟨hmem, hrole⟩, ⟨before, hb, hbefore, hrole⟩, ⟨after, ha, hafter, hrole⟩⟩

omit [LinearOrder Copy] [Fintype Label] in
theorem union_roleScopes (scope : Copy → Finset Label) (role : Finset Label) :
    scopeUnion (roleScopes scope role) = scopeUnion scope ∩ role := by
  ext label
  simp only [scopeUnion, roleScopes, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
  aesop

/-- Fixed occurrences are counted separately in any chosen pool of labels. -/
theorem middle_occurrence_count_role (scope : Copy → Finset Label) (hscope : NoSingletonScopes scope)
    (role : Finset Label) :
    (∑ copy, (middleScopes scope copy ∩ role).card) + 2 * (scopeUnion scope ∩ role).card =
      ∑ copy, (scope copy ∩ role).card := by
  have hh := middle_occurrence_count (roleScopes scope role) (roleScopes_noSingleton scope hscope role)
  simpa only [middle_roleScopes, union_roleScopes, roleScopes] using hh

end Occurrences

end

end AFT.CanonicalMoments

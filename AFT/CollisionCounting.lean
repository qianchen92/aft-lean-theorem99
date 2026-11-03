import AFT.CanonicalMoments

/-!
# Counting actual finite collision patterns

A pattern with exactly `used` labels is encoded by an injective enumeration
of those labels and a word on the occurrence positions.  This retains the
falling-factorial pool factor and has no color-alphabet dependence.
-/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

variable {Slot Pool Copy : Type*} [Fintype Slot] [Fintype Pool] [Fintype Copy]

abbrev PatternsWithLabels (used : ℕ) :=
  {pattern : Copy → Slot ↪ Pool // (usedLabels pattern).card = used}

def labelEnumeration (used : ℕ) (pattern : PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) :
    Fin used ≃ usedLabels pattern.val :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe] using pattern.property.symm)

def collisionCode (used : ℕ) (pattern : PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) :
    (Fin used ↪ Pool) × (Copy × Slot → Fin used) :=
  ((labelEnumeration used pattern).toEmbedding.trans (Function.Embedding.subtype _),
    fun occurrence => (labelEnumeration used pattern).symm
      ⟨pattern.val occurrence.1 occurrence.2,
        Finset.mem_image.mpr ⟨occurrence, Finset.mem_univ _, rfl⟩⟩)

omit [Fintype Pool] in
theorem collisionCode_reconstruct (used : ℕ)
    (pattern : PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used)
    (occurrence : Copy × Slot) :
    (collisionCode used pattern).1 ((collisionCode used pattern).2 occurrence) =
      pattern.val occurrence.1 occurrence.2 := by
  simp [collisionCode]

omit [Fintype Pool] in
theorem collisionCode_injective (used : ℕ) :
    Function.Injective (collisionCode (Slot := Slot) (Pool := Pool) (Copy := Copy) used) := by
  intro first second h
  apply Subtype.ext
  funext copy
  apply Function.Embedding.ext
  intro slot
  have hh := congrArg (fun code : (Fin used ↪ Pool) × (Copy × Slot → Fin used) =>
    code.1 (code.2 (copy, slot))) h
  simpa only [collisionCode_reconstruct] using hh

theorem patternsWithLabels_card_le (used : ℕ) :
    Fintype.card (PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) ≤
      (Fintype.card Pool).descFactorial used * used ^ (Fintype.card Copy * Fintype.card Slot) := by
  have hh := Fintype.card_le_of_injective _ (collisionCode_injective (Slot := Slot) (Pool := Pool) (Copy := Copy) used)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_embedding_eq] using hh

omit [Fintype Pool] in
theorem usedLabels_card_le_occurrences (pattern : Copy → Slot ↪ Pool) :
    (usedLabels pattern).card ≤ Fintype.card Copy * Fintype.card Slot := by
  simpa only [Finset.card_univ, Fintype.card_prod] using
    Finset.card_image_le (s := Finset.univ) (f := fun occurrence : Copy × Slot => pattern occurrence.1 occurrence.2)

theorem patternsWithLabels_card_le_uniform (used : ℕ) :
    Fintype.card (PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) ≤
      (Fintype.card Pool).descFactorial used *
        (Fintype.card Copy * Fintype.card Slot) ^ (Fintype.card Copy * Fintype.card Slot) := by
  by_cases hle : used ≤ Fintype.card Copy * Fintype.card Slot
  · exact (patternsWithLabels_card_le used).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle _))
  · have hempty : IsEmpty (PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) :=
      ⟨fun pattern => hle (pattern.property ▸ usedLabels_card_le_occurrences pattern.val)⟩
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _

theorem noSingletonPatterns_card_le (used : ℕ) :
    (Finset.univ.filter (fun pattern : Copy → Slot ↪ Pool =>
      NoSingleton pattern ∧ (usedLabels pattern).card = used)).card ≤
      (Fintype.card Pool).descFactorial used *
        (Fintype.card Copy * Fintype.card Slot) ^ (Fintype.card Copy * Fintype.card Slot) := by
  apply (Finset.card_le_card (show
    Finset.univ.filter (fun pattern : Copy → Slot ↪ Pool => NoSingleton pattern ∧ (usedLabels pattern).card = used) ⊆
    Finset.univ.filter (fun pattern : Copy → Slot ↪ Pool => (usedLabels pattern).card = used) from
      fun _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2.2⟩)).trans
  simpa only [← Fintype.card_subtype] using patternsWithLabels_card_le_uniform (Slot := Slot) (Pool := Pool) (Copy := Copy) used

omit [Fintype Slot] [Fintype Pool] [Fintype Copy] in
/-- The genuine falling factorial is uniformly comparable to the pool
power at each fixed order, without changing the sampling convention. -/
theorem descFactorial_half_power (population order : ℕ) (hlarge : 2 * order ≤ population) :
    ((population : ℝ) / 2) ^ order ≤ (population.descFactorial order : ℝ) := by
  have hsub : order ≤ population + 1 := by omega
  have hbase : (population : ℝ) / 2 ≤ (population + 1 - order : ℕ) := by
    rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
    have hh : (2 : ℝ) * order ≤ population := by exact_mod_cast hlarge
    linarith
  exact (pow_le_pow_left₀ (by positivity) hbase order).trans
    (by exact_mod_cast Nat.pow_sub_le_descFactorial population order)

omit [Fintype Slot] [Fintype Pool] [Fintype Copy] in
/-- Pool cardinalities cancel against the exact distinct-index denominator.
The remaining constant depends only on the fixed kernel and moment orders. -/
theorem collision_normalizer_bound (population order power used : ℕ)
    (hpopulation : 0 < population) (hlarge : 2 * order ≤ population)
    (hused : used ≤ power * order) :
    (population.descFactorial used : ℝ) * (population : ℝ) ^ (power * order - used) /
        (population.descFactorial order : ℝ) ^ power ≤ (2 : ℝ) ^ (power * order) := by
  have hpos : (0 : ℝ) < population.descFactorial order := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : order ≤ population))
  have hnum : (population.descFactorial used : ℝ) * (population : ℝ) ^ (power * order - used) ≤
      (population : ℝ) ^ (power * order) := by
    calc
      _ ≤ (population : ℝ) ^ used * (population : ℝ) ^ (power * order - used) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.descFactorial_le_pow population used) (by positivity)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hused]
  have hden := pow_le_pow_left₀ (by positivity : 0 ≤ ((population : ℝ) / 2) ^ order)
    (descFactorial_half_power population order hlarge) power
  rw [← pow_mul, Nat.mul_comm order power, div_pow] at hden
  have hden' : (population : ℝ) ^ (power * order) ≤
      (2 : ℝ) ^ (power * order) * (population.descFactorial order : ℝ) ^ power := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (power * order))).mp hden
    simpa only [mul_comm] using hh
  exact (div_le_iff₀ (pow_pos hpos _)).mpr (hnum.trans hden')

end

end AFT.CanonicalMoments

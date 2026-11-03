import AFT.MixedKernel

/-! # Exact finite collision expansion of canonical U-statistic moments -/

namespace AFT
namespace CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color Copy : Type*}
variable [Fintype Slot] [Fintype Pool] [Fintype Color] [Fintype Copy]

/-- Evaluate a genuine joint kernel at distinct sampled pool indices. -/
noncomputable def placedKernel (kernel : (Slot → Color) → ℝ) (placement : Slot ↪ Pool)
    (word : Pool → Color) : ℝ := kernel (word ∘ placement)

omit [Fintype Copy] [Fintype Pool] in
/-- Distinct-index placement preserves actual canonicality on its image. -/
theorem placedKernel_canonical (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Slot => reference) Finset.univ kernel)
    (placement : Slot ↪ Pool) :
    Hoeffding.Canonical (fun _ : Pool => reference) (Finset.univ.map placement)
      (placedKernel kernel placement) := by
  constructor
  · intro first second hequal
    unfold placedKernel
    congr 1
    funext slot
    exact hequal (placement slot) (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩)
  · intro label hlabel
    obtain ⟨slot, _, rfl⟩ := Finset.mem_map.mp hlabel
    intro word
    have hword (color : Color) :
        (Function.update word (placement slot) color) ∘ placement =
          Function.update (word ∘ placement) slot color := by
      funext other
      by_cases hother : other = slot
      · subst other; simp
      · have hne : placement other ≠ placement slot := fun h => hother (placement.injective h)
        simp [Function.comp_apply, Function.update_of_ne hother, Function.update_of_ne hne]
    simp only [placedKernel, hword]
    exact hcanonical.2 slot (Finset.mem_univ _) (word ∘ placement)

/-- The complete product belonging to one labeled moment collision pattern. -/
noncomputable def patternProduct (kernel : (Slot → Color) → ℝ)
    (pattern : Copy → Slot ↪ Pool) (word : Pool → Color) : ℝ :=
  ∏ copy, placedKernel kernel (pattern copy) word

/-- A pool label used by just one occurrence annihilates the entire moment
term, by integrating that actual independent coordinate. -/
theorem pattern_expectation_zero_of_singleton (reference : FiniteDist Color)
    (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Slot => reference) Finset.univ kernel)
    (pattern : Copy → Slot ↪ Pool) (singleCopy : Copy) (singleSlot : Slot)
    (hsingle : ∀ copy, copy ≠ singleCopy → ∀ slot,
      pattern copy slot ≠ pattern singleCopy singleSlot) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation (patternProduct kernel pattern) = 0 := by
  let label := pattern singleCopy singleSlot
  let remainder (word : Pool → Color) :=
    ∏ copy ∈ Finset.univ.erase singleCopy, placedKernel kernel (pattern copy) word
  have hcentered := (placedKernel_canonical reference kernel hcanonical (pattern singleCopy)).2 label
    (Finset.mem_map.mpr ⟨singleSlot, Finset.mem_univ _, rfl⟩)
  have hdepends : Hoeffding.DependsOn (Finset.univ.erase label) remainder := by
    intro first second hequal
    apply Finset.prod_congr rfl
    intro copy hcopy
    unfold placedKernel
    congr 1
    funext slot
    exact hequal (pattern copy slot)
      (Finset.mem_erase.mpr ⟨hsingle copy (Finset.mem_erase.mp hcopy).1 slot, Finset.mem_univ _⟩)
  have h := Hoeffding.orthogonal_of_centered (fun _ : Pool => reference) (Finset.univ.erase label)
    label (by simp) (placedKernel kernel (pattern singleCopy)) remainder hcentered hdepends
  have heq : patternProduct kernel pattern =
      (fun word => placedKernel kernel (pattern singleCopy) word * remainder word) := by
    funext word
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ singleCopy)).symm
  rw [heq]
  exact h

omit [Fintype Copy] in
/-- The ordered, exactly normalized distinct-index U-statistic. -/
noncomputable def statistic (kernel : (Slot → Color) → ℝ) (word : Pool → Color) : ℝ :=
  (∑ placement : Slot ↪ Pool, placedKernel kernel placement word) /
    ((Fintype.card Pool).descFactorial (Fintype.card Slot) : ℝ)

omit [Fintype Copy] in
/-- Every moment expands over actual distinct-index placements with its
exact falling-factorial denominator retained. -/
theorem statistic_moment_expansion (reference : FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (power : ℕ) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation
      (fun word => statistic kernel word ^ power) =
      (∑ pattern : Fin power → Slot ↪ Pool,
        (FiniteDist.independent (fun _ : Pool => reference)).expectation (patternProduct kernel pattern)) /
          ((Fintype.card Pool).descFactorial (Fintype.card Slot) : ℝ) ^ power := by
  unfold statistic FiniteDist.expectation patternProduct
  simp only [div_pow, Fintype.sum_pow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- The pool labels actually used by a moment pattern. -/
noncomputable def usedLabels (pattern : Copy → Slot ↪ Pool) : Finset Pool :=
  Finset.univ.image (fun occurrence : Copy × Slot => pattern occurrence.1 occurrence.2)

/-- A surviving pattern has no sample label occurring in only one kernel. -/
def NoSingleton (pattern : Copy → Slot ↪ Pool) : Prop :=
  ∀ copy slot, ∃ otherCopy otherSlot,
    otherCopy ≠ copy ∧ pattern otherCopy otherSlot = pattern copy slot

/-- Nonzero canonical moment terms necessarily have no singleton sample. -/
theorem noSingleton_of_expectation_ne_zero (reference : FiniteDist Color)
    (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Slot => reference) Finset.univ kernel)
    (pattern : Copy → Slot ↪ Pool)
    (hne : (FiniteDist.independent (fun _ : Pool => reference)).expectation
      (patternProduct kernel pattern) ≠ 0) : NoSingleton pattern := by
  by_contra h
  simp only [NoSingleton, not_forall, not_exists, not_and] at h
  obtain ⟨copy, slot, hsingle⟩ := h
  apply hne
  apply pattern_expectation_zero_of_singleton reference kernel hcanonical pattern copy slot
  intro otherCopy hcopy otherSlot
  exact hsingle otherCopy otherSlot hcopy

omit [Fintype Pool] in
/-- The exact collision support has at most half as many pool labels as
kernel argument occurrences. No pool-size or alphabet factor is discarded. -/
theorem noSingleton_card_bound (pattern : Copy → Slot ↪ Pool)
    (hpattern : NoSingleton pattern) :
    2 * (usedLabels pattern).card ≤ Fintype.card Copy * Fintype.card Slot := by
  let label (occurrence : Copy × Slot) := pattern occurrence.1 occurrence.2
  have hcount : Fintype.card (Copy × Slot) =
      ∑ value ∈ usedLabels pattern, (Finset.univ.filter (fun occurrence : Copy × Slot => label occurrence = value)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro occurrence _
    exact Finset.mem_image.mpr ⟨occurrence, Finset.mem_univ _, rfl⟩
  have htwo (value : Pool) (hvalue : value ∈ usedLabels pattern) :
      2 ≤ (Finset.univ.filter (fun occurrence : Copy × Slot => label occurrence = value)).card := by
    obtain ⟨⟨copy, slot⟩, _, heq⟩ := Finset.mem_image.mp hvalue
    obtain ⟨otherCopy, otherSlot, hcopy, hother⟩ := hpattern copy slot
    have hne : (copy, slot) ≠ (otherCopy, otherSlot) := by
      intro hequal
      exact hcopy (Prod.mk.inj hequal).1.symm
    have hsubset : ({(copy, slot), (otherCopy, otherSlot)} : Finset (Copy × Slot)) ⊆
        Finset.univ.filter (fun occurrence => label occurrence = value) := by
      intro occurrence hoccurrence
      rcases Finset.mem_insert.mp hoccurrence with rfl | hoccurrence
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
      · have hoccurrence := Finset.mem_singleton.mp hoccurrence
        subst occurrence
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother.trans heq⟩
    have hh := Finset.card_le_card hsubset
    simpa [hne] using hh
  have hsum := Finset.sum_le_sum htwo
  simpa only [Finset.sum_const, smul_eq_mul, ← hcount, Fintype.card_prod, mul_comm] using hsum

omit [Fintype Copy] in
/-- The exact even-moment sum may discard all singleton patterns, without
estimating the remaining genuine joint-kernel contractions. -/
theorem statistic_moment_surviving_expansion (reference : FiniteDist Color)
    (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Slot => reference) Finset.univ kernel)
    (power : ℕ) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation
      (fun word => statistic kernel word ^ power) =
      (∑ pattern ∈ Finset.univ.filter (NoSingleton (Copy := Fin power)),
        (FiniteDist.independent (fun _ : Pool => reference)).expectation (patternProduct kernel pattern)) /
          ((Fintype.card Pool).descFactorial (Fintype.card Slot) : ℝ) ^ power := by
  rw [statistic_moment_expansion]
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro pattern _ hnot
  by_contra hne
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    noSingleton_of_expectation_ne_zero reference kernel hcanonical pattern hne⟩)

end CanonicalMoments
end AFT

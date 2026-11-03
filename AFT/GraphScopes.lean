import AFT.CollisionGraph

/-! # The active and fixed coordinates of the actual ordered collision graph -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Label : Type*} [Fintype Label] {count : ℕ}

/-- Extend a finite copy sequence by empty scopes. -/
noncomputable def scopeAt (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  if h : index < count then scope ⟨index, h⟩ else ∅

/-- Labels appearing strictly before a position. -/
noncomputable def scopePrefix (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  Finset.univ.filter (fun label => ∃ copy : Fin count, copy.val < index ∧ label ∈ scope copy)

/-- Labels appearing at or after a position. -/
noncomputable def scopeSuffix (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  Finset.univ.filter (fun label => ∃ copy : Fin count, index ≤ copy.val ∧ label ∈ scope copy)

/-- Integrate a label exactly at its last occurrence. -/
noncomputable def scopeEnding (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  scopeAt scope index \ scopeSuffix scope (index + 1)

/-- Every ended label is absent from all later physical copies. -/
theorem scopeEnding_disjoint (scope : Fin count → Finset Label) (index later : ℕ)
    (hbefore : index < later) (hlater : later < count) :
    Disjoint (scopeEnding scope index) (scopeAt scope later) := by
  apply Finset.disjoint_left.mpr
  intro label hend hl
  have hnot := (Finset.mem_sdiff.mp hend).2
  apply hnot
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ⟨⟨later, hlater⟩, by dsimp only; omega, ?_⟩⟩
  simpa only [scopeAt, dif_pos hlater] using hl

/-- Prefix scopes accumulate by adding the next exact copy scope. -/
theorem scopePrefix_succ (scope : Fin count → Finset Label) (index : ℕ) (hi : index < count) :
    scopePrefix scope (index + 1) = scopePrefix scope index ∪ scopeAt scope index := by
  ext label
  simp only [scopePrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    scopeAt, dif_pos hi, Finset.mem_union]
  constructor
  · rintro ⟨copy, hcopy, hlabel⟩
    by_cases hlt : copy.val < index
    · exact Or.inl ⟨copy, hlt, hlabel⟩
    · right
      have heq : copy = ⟨index, hi⟩ := Fin.ext (by dsimp only; omega)
      simpa only [heq] using hlabel
  · rintro (⟨copy, hcopy, hlabel⟩ | hlabel)
    · exact ⟨copy, by omega, hlabel⟩
    · exact ⟨⟨index, hi⟩, by dsimp only; omega, hlabel⟩

/-- Suffix scopes split into the current copy and the strictly later copies. -/
theorem scopeSuffix_step (scope : Fin count → Finset Label) (index : ℕ) (hi : index < count) :
    scopeSuffix scope index = scopeAt scope index ∪ scopeSuffix scope (index + 1) := by
  ext label
  simp only [scopeSuffix, Finset.mem_filter, Finset.mem_univ, true_and,
    scopeAt, dif_pos hi, Finset.mem_union]
  constructor
  · rintro ⟨copy, hcopy, hlabel⟩
    by_cases heq : copy.val = index
    · left
      have hc : copy = ⟨index, hi⟩ := Fin.ext heq
      simpa only [hc] using hlabel
    · exact Or.inr ⟨copy, by omega, hlabel⟩
  · rintro (hlabel | ⟨copy, hcopy, hlabel⟩)
    · exact ⟨⟨index, hi⟩, le_rfl, hlabel⟩
    · exact ⟨copy, by omega, hlabel⟩

/-- Active variables are exactly those used both before and after the cut. -/
theorem graphActive_eq_prefix_inter_suffix (scope : Fin count → Finset Label)
    (index : ℕ) (hi : index ≤ count) :
    graphActive (scopeAt scope) (scopeEnding scope) index = scopePrefix scope index ∩ scopeSuffix scope index := by
  induction index with
  | zero => simp [graphActive, scopePrefix]
  | succ index ih =>
    have hlt : index < count := by omega
    rw [graphActive, ih (by omega), scopePrefix_succ scope index hlt, scopeSuffix_step scope index hlt]
    ext label
    simp only [scopeEnding, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    tauto

/-- The fixed fiber at a copy consists precisely of its middle occurrences. -/
theorem graphFixed_eq_middle (scope : Fin count → Finset Label) (index : ℕ) (hi : index < count) :
    graphFixed (scopeAt scope) (scopeEnding scope) index =
      scopeAt scope index ∩ scopePrefix scope index ∩ scopeSuffix scope (index + 1) := by
  rw [graphFixed, graphActive_eq_prefix_inter_suffix scope index hi.le, scopeSuffix_step scope index hi]
  ext label
  simp only [scopeEnding, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto

variable {Color : Type*} [Fintype Color]

/-- Extend an actual finite sequence of kernels by zero. -/
noncomputable def kernelAt (kernel : Fin count → (Label → Color) → ℝ) (index : ℕ) : (Label → Color) → ℝ :=
  if h : index < count then kernel ⟨index, h⟩ else fun _ => 0

/-- The graph contraction for the actual finite sequence, with exact
first/last integration and the actual middle-occurrence fibers. -/
theorem finite_graph_product_sq_le (reference : Label → FiniteDist Color)
    (scope : Fin count → Finset Label) (kernel : Fin count → (Label → Color) → ℝ)
    (hkernel : ∀ copy, Hoeffding.DependsOn (scope copy) (kernel copy)) :
    (FiniteDist.independent reference).expectation (fun word => ∏ copy, kernel copy word) ^ 2 ≤
      ∏ copy, MixedKernel.fiberNorm reference (kernel copy)
        (scope copy ∩ scopePrefix scope copy.val ∩ scopeSuffix scope (copy.val + 1)) ^ 2 := by
  have hdepends (index : ℕ) : Hoeffding.DependsOn (scopeAt scope index) (kernelAt kernel index) := by
    by_cases hi : index < count
    · simpa only [scopeAt, kernelAt, dif_pos hi] using hkernel ⟨index, hi⟩
    · intro first second _
      simp only [kernelAt, dif_neg hi]
  have h := graph_product_expectation_sq_le reference (scopeAt scope) (scopeEnding scope)
    (kernelAt kernel) hdepends count (scopeEnding_disjoint scope)
  simp only [Finset.prod_range] at h
  have hfixed (copy : Fin count) : graphFixed (scopeAt scope) (scopeEnding scope) copy.val =
      scope copy ∩ scopePrefix scope copy.val ∩ scopeSuffix scope (copy.val + 1) := by
    rw [graphFixed_eq_middle scope copy.val copy.isLt]
    simp only [scopeAt, dif_pos copy.isLt]
  simpa only [kernelAt, dif_pos (Fin.isLt _), hfixed] using h

end AFT.CanonicalMoments

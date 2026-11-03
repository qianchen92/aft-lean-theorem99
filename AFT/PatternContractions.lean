import AFT.GraphScopes
import AFT.PlacedFibers
import AFT.CollisionOccurrences

/-! # Actual arbitrary-joint-kernel collision contractions in mixed activity -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color] {power : ℕ}

/-- The exact scope of each actual distinct-index copy. -/
noncomputable def patternScopes (pattern : Fin power → Slot ↪ Pool) : Fin power → Finset Pool :=
  fun copy => Finset.univ.map (pattern copy)

/-- The original kernel arguments fixed at the middle occurrences of a pattern. -/
noncomputable def patternFixed (pattern : Fin power → Slot ↪ Pool) (copy : Fin power) : Finset Slot :=
  placementFixed (pattern copy) (middleScopes (patternScopes pattern) copy)

/-- The transfer-chain and occurrence-count definitions of middle labels agree. -/
theorem graph_middle_eq (scope : Fin power → Finset Pool) (copy : Fin power) :
    scope copy ∩ scopePrefix scope copy.val ∩ scopeSuffix scope (copy.val + 1) = middleScopes scope copy := by
  ext label
  simp only [scopePrefix, scopeSuffix, middleScopes, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hlabel, before, hbefore, hbeforeLabel⟩, after, hafter, hafterLabel⟩
    exact ⟨hlabel, ⟨before, hbefore, hbeforeLabel⟩, ⟨after, by change copy.val < after.val; omega, hafterLabel⟩⟩
  · rintro ⟨hlabel, ⟨before, hbefore, hbeforeLabel⟩, ⟨after, hafter, hafterLabel⟩⟩
    exact ⟨⟨hlabel, before, hbefore, hbeforeLabel⟩, after, by exact Nat.succ_le_of_lt hafter, hafterLabel⟩

/-- Every actual collision pattern contracts through its exact mixed fibers.
This applies to arbitrary joint kernels, without any rank-one expansion. -/
theorem pattern_expectation_sq_le (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (pattern : Fin power → Slot ↪ Pool) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation (patternProduct kernel pattern) ^ 2 ≤
      ∏ copy, MixedKernel.fiberNorm (fun _ : Slot => reference) kernel (patternFixed pattern copy) ^ 2 := by
  have hscope (copy : Fin power) : Hoeffding.DependsOn (patternScopes pattern copy)
      (placedKernel kernel (pattern copy)) := by
    intro first second hequal
    unfold placedKernel
    congr 1
    funext slot
    exact hequal (pattern copy slot) (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩)
  have h := finite_graph_product_sq_le (fun _ : Pool => reference) (patternScopes pattern)
    (fun copy => placedKernel kernel (pattern copy)) hscope
  simpa only [graph_middle_eq, placedKernel_fiberNorm, patternFixed, patternProduct] using h

/-- The actual absolute collision term is bounded by the product of its
mixed input fibers, with no cardinality loss. -/
theorem pattern_expectation_abs_le (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (pattern : Fin power → Slot ↪ Pool) :
    |(FiniteDist.independent (fun _ : Pool => reference)).expectation (patternProduct kernel pattern)| ≤
      ∏ copy, MixedKernel.fiberNorm (fun _ : Slot => reference) kernel (patternFixed pattern copy) := by
  have h := pattern_expectation_sq_le reference kernel pattern
  rw [Finset.prod_pow] at h
  exact (sq_le_sq₀ (abs_nonneg _) (Finset.prod_nonneg fun copy _ => MixedKernel.fiberNorm_nonneg _ _ _)).mp
    (by simpa only [sq_abs] using h)

omit [Fintype Color] [Fintype Pool] in
/-- Pullback along an actual placement preserves the cardinality of any set
of labels in its image. -/
theorem placementFixed_card (placement : Slot ↪ Pool) (fixed : Finset Pool)
    (hfixed : fixed ⊆ Finset.univ.map placement) : (placementFixed placement fixed).card = fixed.card := by
  have heq : (placementFixed placement fixed).map placement = fixed := by
    ext label
    constructor
    · intro h
      obtain ⟨slot, hslot, rfl⟩ := Finset.mem_map.mp h
      exact (Finset.mem_filter.mp hslot).2
    · intro h
      obtain ⟨slot, _, heq⟩ := Finset.mem_map.mp (hfixed h)
      refine Finset.mem_map.mpr ⟨slot, ?_, heq⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [heq] using h⟩
  have h := congrArg Finset.card heq
  simpa only [Finset.card_map] using h

omit [Fintype Color] [Fintype Pool] in
theorem patternScopes_noSingleton (pattern : Fin power → Slot ↪ Pool) (hpattern : NoSingleton pattern) :
    NoSingletonScopes (patternScopes pattern) := by
  intro copy label hlabel
  obtain ⟨slot, _, rfl⟩ := Finset.mem_map.mp hlabel
  obtain ⟨other, otherSlot, hother, heq⟩ := hpattern copy slot
  exact ⟨other, hother, Finset.mem_map.mpr ⟨otherSlot, Finset.mem_univ _, heq⟩⟩

omit [Fintype Color] [Fintype Pool] in
theorem patternScopes_union (pattern : Fin power → Slot ↪ Pool) :
    scopeUnion (patternScopes pattern) = usedLabels pattern := by
  ext label
  simp only [scopeUnion, patternScopes, usedLabels, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_map, Finset.mem_image, Prod.exists]

omit [Fintype Color] in
/-- Each used pool label contributes exactly two integrated occurrences;
all remaining occurrences give precisely the fixed-fiber penalties. -/
theorem patternFixed_card_sum (pattern : Fin power → Slot ↪ Pool) (hpattern : NoSingleton pattern) :
    (∑ copy, (patternFixed pattern copy).card) + 2 * (usedLabels pattern).card =
      power * Fintype.card Slot := by
  have hcard (copy : Fin power) : (patternFixed pattern copy).card =
      (middleScopes (patternScopes pattern) copy).card :=
    placementFixed_card (pattern copy) _ (by
      intro label hlabel
      simp only [middleScopes, Finset.mem_filter] at hlabel
      exact hlabel.1)
  simp only [hcard]
  have h := middle_occurrence_count (patternScopes pattern) (patternScopes_noSingleton pattern hpattern)
  simpa only [patternScopes_union, patternScopes, Finset.card_map, Finset.card_univ,
    Finset.sum_const, Fintype.card_fin, smul_eq_mul] using h

end AFT.CanonicalMoments

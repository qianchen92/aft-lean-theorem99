import AFT.PatternContractions

/-! # Mixed fibers for unequal pools with their actual separate reference laws -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]

/-- Reindexing a nonidentical product law transports every coordinate law. -/
theorem independent_equiv_expectation_general (equiv : Slot ≃ Pool)
    (reference : Pool → FiniteDist Color) (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent reference).expectation (fun word => function (word ∘ equiv)) =
      (FiniteDist.independent (fun slot => reference (equiv slot))).expectation function := by
  have h := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word => (∏ slot, (reference (equiv slot)).weight (word slot)) * function word)
  unfold FiniteDist.expectation FiniteDist.independent
  apply Eq.trans ?_ h
  apply Finset.sum_congr (by ext; simp)
  intro word _
  change (∏ slot, (reference slot).weight (word slot)) * function (word ∘ equiv) =
    (∏ slot, (reference (equiv slot)).weight ((word ∘ equiv) slot)) * function (word ∘ equiv)
  congr 1
  exact (equiv.prod_comp (fun slot => (reference slot).weight (word slot))).symm

/-- The exact law of an arbitrary injective subword of nonidentical inputs. -/
theorem independent_embedding_expectation_general (reference : Pool → FiniteDist Color)
    (placement : Slot ↪ Pool) (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent reference).expectation (fun word => function (word ∘ placement)) =
      (FiniteDist.independent (fun slot => reference (placement slot))).expectation function := by
  have hr := LocalTensors.independent_restriction_expectation reference (Finset.univ.map placement)
    (fun word => function (word ∘ placementEquiv placement))
  have he := independent_equiv_expectation_general (placementEquiv placement)
    (fun label : Finset.univ.map placement => reference label) function
  apply Eq.trans ?_ (hr.trans ?_)
  · rfl
  · apply Eq.trans ?_ he
    unfold FiniteDist.expectation FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rfl

/-- Every placed frozen fiber uses its actual coordinate-specific laws. -/
theorem placedKernel_fiberSq_general (reference : Pool → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (placement : Slot ↪ Pool) (fixed : Finset Pool) (word : Pool → Color) :
    MixedKernel.fiberSq reference (placedKernel kernel placement) fixed word =
      MixedKernel.fiberSq (fun slot => reference (placement slot)) kernel
        (placementFixed placement fixed) (word ∘ placement) := by
  have hfreeze (integrated : Pool → Color) : MixedKernel.freeze fixed word integrated ∘ placement =
      MixedKernel.freeze (placementFixed placement fixed) (word ∘ placement) (integrated ∘ placement) := by
    funext slot
    simp [MixedKernel.freeze, placementFixed]
  simp only [MixedKernel.fiberSq, FiniteDist.l2Sq, placedKernel, hfreeze]
  exact independent_embedding_expectation_general reference placement
    (fun integrated => kernel (MixedKernel.freeze (placementFixed placement fixed) (word ∘ placement) integrated) ^ 2)

/-- Exact mixed-fiber norm transport for coordinate-compatible pool labels. -/
theorem placedKernel_fiberNorm_general [Nonempty Color] (reference : Pool → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (placement : Slot ↪ Pool) (fixed : Finset Pool) :
    MixedKernel.fiberNorm reference (placedKernel kernel placement) fixed =
      MixedKernel.fiberNorm (fun slot => reference (placement slot)) kernel (placementFixed placement fixed) := by
  simp only [MixedKernel.fiberNorm, placedKernel_fiberSq_general]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro word
    exact norm_le_pi_norm (fun word => Real.sqrt (MixedKernel.fiberSq (fun slot => reference (placement slot))
      kernel (placementFixed placement fixed) word)) (word ∘ placement)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro word
    let extended : Pool → Color := Function.extend placement word (fun _ => Classical.choice inferInstance)
    have heq : extended ∘ placement = word := by
      funext slot
      exact placement.injective.extend_apply word (fun _ : Pool => Classical.choice (inferInstance : Nonempty Color)) slot
    have hh := norm_le_pi_norm (fun values => Real.sqrt (MixedKernel.fiberSq (fun slot => reference (placement slot))
      kernel (placementFixed placement fixed) (values ∘ placement))) extended
    simpa only [heq] using hh

/-- The actual graph contraction for unequal pools and compatible coordinate
laws. The input can be any joint kernel across all its primary and body slots. -/
theorem pattern_expectation_sq_le_compatible [Nonempty Color] {power : ℕ}
    (reference : Pool → FiniteDist Color) (inputReference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (pattern : Fin power → Slot ↪ Pool)
    (hcompatible : ∀ copy slot, reference (pattern copy slot) = inputReference slot) :
    (FiniteDist.independent reference).expectation (patternProduct kernel pattern) ^ 2 ≤
      ∏ copy, MixedKernel.fiberNorm inputReference kernel (patternFixed pattern copy) ^ 2 := by
  have hscope (copy : Fin power) : Hoeffding.DependsOn (patternScopes pattern copy)
      (placedKernel kernel (pattern copy)) := by
    intro first second hequal
    unfold placedKernel
    congr 1
    funext slot
    exact hequal (pattern copy slot) (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩)
  have h := finite_graph_product_sq_le reference (patternScopes pattern)
    (fun copy => placedKernel kernel (pattern copy)) hscope
  have hreference (copy : Fin power) : (fun slot => reference (pattern copy slot)) = inputReference :=
    funext (hcompatible copy)
  simpa only [graph_middle_eq, placedKernel_fiberNorm_general, hreference, patternFixed, patternProduct] using h

end AFT.CanonicalMoments

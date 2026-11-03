import AFT.CanonicalVariance

/-! # Actual mixed fibers of a distinct-index placement -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]

/-- The actual injective placement identifies its slot set with its image. -/
noncomputable def placementEquiv (placement : Slot ↪ Pool) : Slot ≃ (Finset.univ.map placement) :=
  Equiv.ofBijective (fun slot => ⟨placement slot, Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro first second heq
      exact placement.injective (congrArg Subtype.val heq)
    · intro label
      obtain ⟨slot, _, heq⟩ := Finset.mem_map.mp label.property
      exact ⟨slot, Subtype.ext heq⟩)

/-- Every finite injective subword has exactly the original independent law. -/
theorem independent_embedding_expectation (reference : FiniteDist Color) (placement : Slot ↪ Pool)
    (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation (fun word => function (word ∘ placement)) =
      (FiniteDist.independent (fun _ : Slot => reference)).expectation function := by
  have hr := LocalTensors.independent_restriction_expectation
    (fun _ : Pool => reference) (Finset.univ.map placement)
      (fun word => function (word ∘ placementEquiv placement))
  have he := independent_equiv_expectation (placementEquiv placement) reference function
  apply Eq.trans ?_ (hr.trans ?_)
  · rfl
  · apply Eq.trans ?_ he
    unfold FiniteDist.expectation FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rfl

/-- Pull a set of fixed pool labels back to genuine kernel arguments. -/
noncomputable def placementFixed (placement : Slot ↪ Pool) (fixed : Finset Pool) : Finset Slot :=
  Finset.univ.filter (fun slot => placement slot ∈ fixed)

/-- Exact fiber-square identification; all unused pool labels integrate out. -/
theorem placedKernel_fiberSq (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (placement : Slot ↪ Pool) (fixed : Finset Pool) (word : Pool → Color) :
    MixedKernel.fiberSq (fun _ : Pool => reference) (placedKernel kernel placement) fixed word =
      MixedKernel.fiberSq (fun _ : Slot => reference) kernel (placementFixed placement fixed) (word ∘ placement) := by
  have hfreeze (integrated : Pool → Color) : MixedKernel.freeze fixed word integrated ∘ placement =
      MixedKernel.freeze (placementFixed placement fixed) (word ∘ placement) (integrated ∘ placement) := by
    funext slot
    simp [MixedKernel.freeze, placementFixed]
  simp only [MixedKernel.fiberSq, FiniteDist.l2Sq, placedKernel, hfreeze]
  exact independent_embedding_expectation reference placement
    (fun integrated => kernel (MixedKernel.freeze (placementFixed placement fixed) (word ∘ placement) integrated) ^ 2)

/-- Placement does not change any prescribed mixed fiber norm. -/
theorem placedKernel_fiberNorm (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (placement : Slot ↪ Pool) (fixed : Finset Pool) :
    MixedKernel.fiberNorm (fun _ : Pool => reference) (placedKernel kernel placement) fixed =
      MixedKernel.fiberNorm (fun _ : Slot => reference) kernel (placementFixed placement fixed) := by
  simp only [MixedKernel.fiberNorm, placedKernel_fiberSq]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro word
    exact norm_le_pi_norm (fun word => Real.sqrt (MixedKernel.fiberSq (fun _ : Slot => reference)
      kernel (placementFixed placement fixed) word)) (word ∘ placement)
  · haveI : Nonempty Color := by
      by_contra h
      haveI : IsEmpty Color := not_nonempty_iff.mp h
      have hh := reference.sum_one
      simp at hh
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro word
    let extended : Pool → Color := Function.extend placement word (fun _ => Classical.choice inferInstance)
    have heq : extended ∘ placement = word := by
      funext slot
      exact placement.injective.extend_apply word (fun _ : Pool => Classical.choice (inferInstance : Nonempty Color)) slot
    have hh := norm_le_pi_norm (fun values => Real.sqrt (MixedKernel.fiberSq (fun _ : Slot => reference)
      kernel (placementFixed placement fixed) (values ∘ placement))) extended
    simpa only [heq] using hh

end AFT.CanonicalMoments

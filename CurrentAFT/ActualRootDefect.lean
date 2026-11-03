import CurrentAFT.ActualRootResponse

/-! # The complete finite root defect at one actual control selection -/
namespace CurrentAFT.ActualRootDefect
open AFT ActualBlockFock TaggedSelection PairedRootPlacement ControlCoordinates
  GradedControlAlgebra LocalCoefficientFamily GradedInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def selectedDefect {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s →ₗ[ℝ]
      Family security order :=
  ∑ tagged ∈ (Finset.univ : Finset (Finset (BlockIndex security))).filter (fun tagged => 2 ≤ tagged.card),
    ActualRootResponse.response order horder queue selection tagged layout

theorem selectedDefect_eq_small {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    selectedDefect order horder queue selection layout =
      ∑ tagged ∈ (Finset.univ : Finset (Finset (BlockIndex security))).filter
          (fun tagged => 2 ≤ tagged.card ∧ tagged.card ≤ order),
        ActualRootResponse.response order horder queue selection tagged layout := by
  unfold selectedDefect
  symm
  apply Finset.sum_subset
  · intro tagged htagged
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp htagged).2.1⟩
  · intro tagged htagged hnot
    have hlower := (Finset.mem_filter.mp htagged).2
    have hlarge : order < tagged.card := by
      have hn : ¬ (2 ≤ tagged.card ∧ tagged.card ≤ order) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
      omega
    exact ActualRootResponse.response_zero_of_order_lt_card order horder queue selection tagged layout hlarge

theorem selectedDefect_vanishesBelow_two {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order 2
      (selectedDefect order horder queue selection layout kernel) := by
  intro arity hsmall
  simp only [selectedDefect, LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro tagged htagged
  have hlower := (Finset.mem_filter.mp htagged).2
  have hdegree := PairedRootDegrees.tags_le_degree selection tagged
  exact ActualRootResponse.response_degree order horder queue selection tagged layout kernel arity (by omega)

theorem selectedDefect_zero_constant {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    (selectedDefect order horder queue selection layout kernel) (zeroArity order) = 0 :=
  selectedDefect_vanishesBelow_two order horder queue selection layout kernel (zeroArity order) (by
    change 0 + 0 < 2
    omega)

end
end CurrentAFT.ActualRootDefect

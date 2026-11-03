import CurrentAFT.ActualRootFamily

/-! # Polynomial-size root-tag enumeration in the actual full response

All subsets with at most the fixed truncation order are generated as the
images of bounded-length words. The algorithm never forms the powerset
of the body population before filtering it by cardinality.
-/
namespace CurrentAFT.FullResponseEnumeration

open AFT ActualBlockFock ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev SubsetWords (Pool : Type*) (order : ℕ) := (size : Fin (order + 1)) × (Fin size.val → Pool)

def boundedSubsets (Pool : Type*) [Fintype Pool] [DecidableEq Pool] (order : ℕ) : Finset (Finset Pool) :=
  (Finset.univ : Finset (SubsetWords Pool order)).image (fun word => Finset.univ.image word.2)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

theorem mem_boundedSubsets {Pool : Type*} [Fintype Pool] [DecidableEq Pool]
    (order : ℕ) (subset : Finset Pool) : subset ∈ boundedSubsets Pool order ↔ subset.card ≤ order := by
  constructor
  · intro hsubset
    obtain ⟨word, _, rfl⟩ := Finset.mem_image.mp hsubset
    have hc := Finset.card_image_le (s := (Finset.univ : Finset (Fin word.1.val))) (f := word.2)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    exact hc.trans (by have := word.1.isLt; omega)
  · intro hcard
    let number : Fin subset.card ≃ subset :=
      (Fintype.equivFinOfCardEq (show Fintype.card subset = subset.card by simp)).symm
    let word : SubsetWords Pool order := ⟨⟨subset.card, by omega⟩, fun index => (number index).val⟩
    refine Finset.mem_image.mpr ⟨word, Finset.mem_univ _, ?_⟩
    ext point
    constructor
    · intro hpoint
      obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hpoint
      exact (number index).property
    · intro hpoint
      refine Finset.mem_image.mpr ⟨number.symm ⟨point, hpoint⟩, Finset.mem_univ _, ?_⟩
      exact congrArg Subtype.val (number.apply_symm_apply ⟨point, hpoint⟩)

theorem subsetWords_card {Pool : Type*} [Fintype Pool] (order : ℕ) (hpool : 1 ≤ Fintype.card Pool) :
    Fintype.card (SubsetWords Pool order) ≤ (order + 1) * (Fintype.card Pool)^order := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _size : Fin (order + 1), (Fintype.card Pool)^order := by
      apply Finset.sum_le_sum
      intro size _
      simp only [Fintype.card_fun, Fintype.card_fin]
      exact Nat.pow_le_pow_right hpool (by have := size.isLt; omega)
    _ = _ := by simp

theorem boundedSubsets_card {Pool : Type*} [Fintype Pool] [DecidableEq Pool]
    (order : ℕ) (hpool : 1 ≤ Fintype.card Pool) :
    (boundedSubsets Pool order).card ≤ (order + 1) * (Fintype.card Pool)^order := by
  exact (Finset.card_image_le).trans
    ((by simp only [Finset.card_univ] :
      (Finset.univ : Finset (SubsetWords Pool order)).card = Fintype.card (SubsetWords Pool order)).le.trans
      (subsetWords_card order hpool))

theorem selectedDefect_bounded {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : TaggedSelection.Selection security r s)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    ActualRootDefect.selectedDefect order horder queue selection layout =
      ∑ tagged ∈ (boundedSubsets (BlockIndex security) order).filter (fun tagged => 2 ≤ tagged.card),
        ActualRootResponse.response order horder queue selection tagged layout := by
  rw [ActualRootDefect.selectedDefect_eq_small]
  have hsets : (Finset.univ : Finset (Finset (BlockIndex security))).filter
      (fun tagged => 2 ≤ tagged.card ∧ tagged.card ≤ order) =
      (boundedSubsets (BlockIndex security) order).filter (fun tagged => 2 ≤ tagged.card) := by
    ext tagged
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_boundedSubsets, and_comm]
  rw [hsets]

theorem block_card (security : ℕ) : Fintype.card (BlockIndex security) = Parameters.bodySize security := by
  have hroom := ProposalPrimary.population_room security
  simp only [BlockIndex, Fintype.card_sum, Fintype.card_fin, centerCount]
  omega

theorem current_subsetWords_polynomial (security order : ℕ) :
    Fintype.card (SubsetWords (BlockIndex security) order) ≤
      ((order + 1) * 131074^order) * Parameters.base security^(160 * order) := by
  have hp : 1 ≤ Fintype.card (BlockIndex security) := by
    rw [block_card]
    have := CycleRootExpansion.current_body_two_le security
    omega
  apply (subsetWords_card order hp).trans
  rw [block_card]
  have hbody : Parameters.bodySize security ≤ 131074 * Parameters.base security^160 := by
    have hd := (Parameters.dimension_bounds security).2
    have hle : Parameters.bodySize security ≤ Parameters.dimension security := by unfold Parameters.dimension; omega
    exact hle.trans hd
  calc
    _ ≤ (order + 1) * (131074 * Parameters.base security^160)^order :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbody _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end
end CurrentAFT.FullResponseEnumeration

import CurrentAFT.UniformTaggedOutput

/-! # Exact product of the unselected public groups and queue blocks -/
namespace CurrentAFT.PairedKeptProduct
open AFT ActualBlockFock TaggedSelection UniformTaggedOutput
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool

theorem primary_removed {security r s : ℕ} (choice : Choice security r s)
    (index : Fin (Parameters.legCount security)) :
    Sum.inl index ∈ (selection security r s choice).removed ↔ index ∈ Finset.univ.map choice.1 := by
  simp [Selection.removed, Selection.removedEmbedding, selection, Finset.mem_map,
    RemovedLabel, Sum.exists]

theorem compensator_removed {security r s : ℕ} (choice : Choice security r s)
    (index : Fin (Parameters.legCount security)) :
    Sum.inr (Sum.inl (compensatorPosition security index)) ∈ (selection security r s choice).removed ↔
      index ∈ Finset.univ.map choice.1 := by
  simp [Selection.removed, Selection.removedEmbedding, selection, Finset.mem_map,
    RemovedLabel, Sum.exists, compensatorPosition, ordinaryPosition,
    Function.Embedding.trans_apply]

theorem ordinary_removed {security r s : ℕ} (choice : Choice security r s)
    (index : Fin (BackgroundRates.ordinaryPool security)) :
    Sum.inr (Sum.inl (ordinaryPosition security index)) ∈ (selection security r s choice).removed ↔
      index ∈ Finset.univ.map choice.2 := by
  simp [Selection.removed, Selection.removedEmbedding, selection, Finset.mem_map,
    RemovedLabel, Sum.exists, compensatorPosition, ordinaryPosition,
    Function.Embedding.trans_apply]

theorem queue_not_removed {security r s : ℕ} (choice : Choice security r s)
    (index : Fin (Parameters.modulus security)) :
    Sum.inr (Sum.inr index) ∉ (selection security r s choice).removed := by
  simp [Selection.removed, Selection.removedEmbedding, selection, Finset.mem_map,
    RemovedLabel, Sum.exists]

variable {Monoid : Type*} [CommMonoid Monoid]

theorem centerSplit_inl (security : ℕ) (index : Fin (Parameters.legCount security)) :
    centerSplit security (.inl index) = compensatorPosition security index := rfl

theorem centerSplit_inr (security : ℕ) (index : Fin (BackgroundRates.ordinaryPool security)) :
    centerSplit security (.inr index) = ordinaryPosition security index := rfl

theorem kept_product {security r s : ℕ} (choice : Choice security r s)
    (factor : BlockIndex security → Monoid) :
    (∏ index : (selection security r s choice).kept, factor index.val) =
      (∏ index : {i : Fin (Parameters.legCount security) // i ∉ Finset.univ.map choice.1},
        factor (.inl index.val) * factor (.inr (.inl (compensatorPosition security index.val)))) *
      (∏ index : {i : Fin (BackgroundRates.ordinaryPool security) // i ∉ Finset.univ.map choice.2},
        factor (.inr (.inl (ordinaryPosition security index.val)))) *
      (∏ index : Fin (Parameters.modulus security), factor (.inr (.inr index))) := by
  rw [← Finset.prod_subtype (selection security r s choice).kept (fun _ => Iff.rfl)]
  rw [Selection.kept, Finset.sdiff_eq_filter, Finset.prod_filter]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  rw [← Equiv.prod_comp (centerSplit security)
    (fun index => if Sum.inr (Sum.inl index) ∉ (selection security r s choice).removed
      then factor (.inr (.inl index)) else 1)]
  rw [Fintype.prod_sum_type]
  simp only [centerSplit_inl, centerSplit_inr, primary_removed,
    compensator_removed, ordinary_removed, queue_not_removed, not_false_eq_true, if_true]
  have hsubtype {Index : Type} [Fintype Index] [DecidableEq Index] (excluded : Finset Index) (f : Index → Monoid) :
      (∏ index, if index ∉ excluded then f index else 1) =
        ∏ index : {i // i ∉ excluded}, f index.val := by
    rw [← Finset.prod_filter]
    exact Finset.prod_subtype _ (fun _ => by simp) _
  simp_rw [hsubtype]
  rw [Finset.prod_mul_distrib]
  ac_rfl

end
end CurrentAFT.PairedKeptProduct

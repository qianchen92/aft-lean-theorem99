import AFT.WeightedPoolChannel
import AFT.FinitePairedPools

/-! # Exact completion of retained public coordinates by their product laws -/
namespace AFT.FiniteDist
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance completionSumDecEq {A B : Type*} : DecidableEq (A ⊕ B) := Classical.decEq _
local instance completionSubtypeDecEq {A : Type*} {p : A → Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable {Selected Pool Color : Type*} [Fintype Selected] [Fintype Pool] [Fintype Color]

private theorem independent_decEq {Index Alphabet : Type*} [Fintype Index] [Fintype Alphabet]
    (first second : DecidableEq Index) (law : Index → FiniteDist Alphabet) (value : (Index → Alphabet) → ℝ) :
    @FiniteDist.expectation (Index → Alphabet) (@Pi.instFintype Index (fun _ => Alphabet) first _ (fun _ => inferInstance))
      (@FiniteDist.independent Alphabet Index _ _ first law) value=
    @FiniteDist.expectation (Index → Alphabet) (@Pi.instFintype Index (fun _ => Alphabet) second _ (fun _ => inferInstance))
      (@FiniteDist.independent Alphabet Index _ _ second law) value := by
  cases Subsingleton.elim first second
  rfl

/-- Keep every selected coordinate, drawing precisely the remaining ones. -/
def embeddingCompletion (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (selected : Selected → Color) : FiniteDist (Pool → Color) :=
  (independent (fun rest : {slot : Pool // slot∉Finset.univ.map embedding} => reference rest.val)).map
    (fun rest => Sum.elim selected rest ∘ (placementPartition embedding).symm)

theorem embeddingCompletion_expectation (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (selected : Selected → Color) (value : (Pool → Color) → ℝ) :
    (embeddingCompletion embedding reference selected).expectation value=
      (independent (fun rest : {slot : Pool // slot∉Finset.univ.map embedding} => reference rest.val)).expectation
        (fun rest => value (Sum.elim selected rest ∘ (placementPartition embedding).symm)) := by
  exact expectation_map _ _ _

/-- The product reference is the actual selected-product mixture of its
conditional completion laws. -/
theorem independent_embedding_completion (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (value : (Pool → Color) → ℝ) :
    (independent reference).expectation value=
      (independent (fun selected => reference (embedding selected))).expectation
        (fun selected => (embeddingCompletion embedding reference selected).expectation value) := by
  let e := placementPartition embedding
  let f := fun word : Selected ⊕ {slot : Pool // slot∉Finset.univ.map embedding} → Color =>
    value (word ∘ e.symm)
  have hh := independent_equiv_expectation_general e reference f
  have hv : (fun word : Pool → Color => f (word ∘ e))=value := by
    funext word
    apply congrArg value
    funext slot
    exact congrArg word (e.apply_symm_apply slot)
  rw [hv] at hh
  have hr : (fun slot => reference (e slot))=Sum.elim
      (fun slot : Selected => reference (embedding slot))
      (fun slot : {slot : Pool // slot∉Finset.univ.map embedding} => reference slot.val) := by
    funext slot
    cases slot <;> rfl
  rw [hr] at hh
  have hs := expectation_independent_sum
    (fun slot : Selected => reference (embedding slot))
    (fun slot : {slot : Pool // slot∉Finset.univ.map embedding} => reference slot.val) f
  have hx := hh.trans ((independent_decEq _ _ _ _).trans hs)
  simpa only [embeddingCompletion_expectation] using hx

/-- A fixed retained score is unaffected by the independently completed
coordinates, for an arbitrary joint observable on the whole word. -/
theorem weighted_embedding_completion (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (score : (Selected → Color) → ℝ) (value : (Pool → Color) → ℝ) :
    (independent reference).expectation (fun word => score (word ∘ embedding)*value word)=
    (independent (fun selected => reference (embedding selected))).expectation
      (fun selected => score selected*(embeddingCompletion embedding reference selected).expectation value) := by
  rw [independent_embedding_completion embedding]
  apply congrArg (expectation (independent (fun selected => reference (embedding selected))))
  funext selected
  simp only [embeddingCompletion_expectation]
  have he (rest : {slot : Pool // slot∉Finset.univ.map embedding} → Color) :
      (Sum.elim selected rest ∘ (placementPartition embedding).symm) ∘ embedding=selected := by
    funext slot
    change Sum.elim selected rest ((placementPartition embedding).symm (embedding slot))=selected slot
    rw [← placementPartition_inl embedding slot,Equiv.symm_apply_apply]
    rfl
  simp only [he,expectation_const_mul]

def completionCoordinate (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (selected : Selected → Color) (slot : Pool) : FiniteDist Color :=
  match (placementPartition embedding).symm slot with
  | .inl index => pointLaw (selected index)
  | .inr index => reference index.val

omit [Fintype Pool] in
@[simp] theorem completionCoordinate_selected (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (selected : Selected → Color) (slot : Selected) :
    completionCoordinate embedding reference selected (embedding slot)=pointLaw (selected slot) := by
  unfold completionCoordinate
  rw [← placementPartition_inl embedding slot,Equiv.symm_apply_apply]

omit [Fintype Pool] in
@[simp] theorem completionCoordinate_other (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (selected : Selected → Color) (slot : {slot : Pool // slot∉Finset.univ.map embedding}) :
    completionCoordinate embedding reference selected slot.val=reference slot.val := by
  unfold completionCoordinate
  rw [← placementPartition_inr embedding slot,Equiv.symm_apply_apply]
  rfl

private theorem independent_product_expectation (reference : Pool → FiniteDist Color)
    (value : Pool → Color → ℝ) :
    (independent reference).expectation (fun word => ∏ index,value index (word index))=
      ∏ index,(reference index).expectation (value index) := by
  unfold expectation independent
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun index color => (reference index).weight color*value index color)).symm

/-- The completion has the actual independent coordinate laws: retained
coordinates are deterministic, and only the rest use the original laws. -/
theorem embeddingCompletion_product (embedding : Selected ↪ Pool) (reference : Pool → FiniteDist Color)
    (selected : Selected → Color) (value : Pool → Color → ℝ) :
    (embeddingCompletion embedding reference selected).expectation (fun word => ∏ slot,value slot (word slot))=
      ∏ slot,(completionCoordinate embedding reference selected slot).expectation (value slot) := by
  rw [embeddingCompletion_expectation]
  have hv (rest : {slot : Pool // slot∉Finset.univ.map embedding} → Color) :
      (∏ slot,value slot ((Sum.elim selected rest ∘ (placementPartition embedding).symm) slot))=
      (∏ slot : Selected,value (embedding slot) (selected slot))*
        ∏ slot : {slot : Pool // slot∉Finset.univ.map embedding},value slot.val (rest slot) := by
    have h := (placementPartition embedding).prod_comp (fun slot =>
      value slot ((Sum.elim selected rest ∘ (placementPartition embedding).symm) slot))
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,Fintype.prod_sum_type,
      placementPartition_inl,placementPartition_inr,Sum.elim_inl,Sum.elim_inr] using h.symm
  simp_rw [hv]
  rw [expectation_const_mul,independent_product_expectation]
  have h := (placementPartition embedding).prod_comp (fun slot =>
    (completionCoordinate embedding reference selected slot).expectation (value slot))
  simpa only [Fintype.prod_sum_type,placementPartition_inl,placementPartition_inr,
    completionCoordinate_selected,completionCoordinate_other,pointLaw_expectation] using h

end
end AFT.FiniteDist

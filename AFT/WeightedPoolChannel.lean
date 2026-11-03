import AFT.FiniteJointExpectation
import AFT.TwoPoolCanonical

/-! # A placed joint score through the complete independent public channel -/
namespace AFT.FiniteDist
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance weightedPoolSumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
private theorem independent_decEq {Index Color : Type*} [Fintype Index] [Fintype Color]
    (first second : DecidableEq Index) (law : Index → FiniteDist Color) (value : (Index → Color) → ℝ) :
    @FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) first _ (fun _ => inferInstance))
      (@FiniteDist.independent Color Index _ _ first law) value=
    @FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) second _ (fun _ => inferInstance))
      (@FiniteDist.independent Color Index _ _ second law) value := by
  cases Subsingleton.elim first second
  rfl

private theorem sum_instance_eq {Index : Type*} (first second : Fintype Index) (value : Index → ℝ) :
    @Finset.sum Index ℝ _ (@Finset.univ _ first) value=
      @Finset.sum Index ℝ _ (@Finset.univ _ second) value := by
  cases Subsingleton.elim first second
  rfl

variable {Selected Rest Pool Color : Type*} [Fintype Selected] [Fintype Rest]
  [Fintype Pool] [Fintype Color]

/-- Integrating every unselected public coordinate gives its actual local
output mass. The selected score is allowed to be an arbitrary joint kernel. -/
theorem expectation_split_product (partition : Selected ⊕ Rest ≃ Pool)
    (law : Pool → FiniteDist Color) (score : (Selected → Color) → ℝ)
    (physical : Pool → Color → ℝ) :
    (independent law).expectation (fun word =>
      score (fun slot => word (partition (.inl slot)))*∏ slot,physical slot (word slot))=
    (independent (fun slot : Selected => law (partition (.inl slot)))).expectation
      (fun word => score word*∏ slot,physical (partition (.inl slot)) (word slot))*
      ∏ slot : Rest,(law (partition (.inr slot))).expectation (physical (partition (.inr slot))) := by
  let value : (Selected ⊕ Rest → Color) → ℝ := fun word =>
    score (word ∘ Sum.inl)*∏ slot,physical (partition slot) (word slot)
  have he := independent_equiv_expectation_general partition law value
  have hl : (fun word : Pool → Color => value (word ∘ partition))=
      fun word => score (fun slot => word (partition (.inl slot)))*∏ slot,physical slot (word slot) := by
    funext word
    dsimp only [value,Function.comp_def]
    exact congrArg (fun x : ℝ => score (fun slot => word (partition (.inl slot)))*x)
      (partition.prod_comp (fun slot => physical slot (word slot)))
  rw [hl] at he
  rw [he]
  have href : (fun slot => law (partition slot))=Sum.elim
      (fun slot : Selected => law (partition (.inl slot))) (fun slot : Rest => law (partition (.inr slot))) := by
    funext slot; cases slot <;> rfl
  rw [href]
  have hsplit := expectation_independent_sum (fun slot : Selected => law (partition (.inl slot)))
    (fun slot : Rest => law (partition (.inr slot))) value
  trans (independent (fun slot : Selected => law (partition (.inl slot)))).expectation
    (fun first => (independent (fun slot : Rest => law (partition (.inr slot)))).expectation
      (fun second => value (Sum.elim first second)))
  · exact (independent_decEq _ _ _ _).trans hsplit
  have hpoint (first : Selected → Color) (second : Rest → Color) :
      value (Sum.elim first second)=
      (score first*∏ slot,physical (partition (.inl slot)) (first slot))*
        ∏ slot,physical (partition (.inr slot)) (second slot) := by
    simp only [value,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
    simp only [Function.comp_def,Sum.elim_inl,mul_assoc]
  simp_rw [hpoint,expectation_const_mul]
  have hprod : (independent (fun slot : Rest => law (partition (.inr slot)))).expectation
      (fun word => ∏ slot,physical (partition (.inr slot)) (word slot))=
      ∏ slot : Rest,(law (partition (.inr slot))).expectation (physical (partition (.inr slot))) := by
    unfold expectation independent
    simp only [← Finset.prod_mul_distrib]
    have hh := (Fintype.prod_sum (fun slot : Rest => fun color : Color =>
      (law (partition (.inr slot))).weight color*physical (partition (.inr slot)) color)).symm
    exact (sum_instance_eq _ _ _).trans hh
  rw [hprod,expectation_mul_const]

def placementPartition (embedding : Selected ↪ Pool) :
    Selected ⊕ {slot : Pool // slot∉Finset.univ.map embedding} ≃ Pool :=
  (Equiv.sumCongr (placementEquiv embedding) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun slot => slot∈Finset.univ.map embedding))

omit [Fintype Pool] in
@[simp] theorem placementPartition_inl (embedding : Selected ↪ Pool) (slot : Selected) :
    placementPartition embedding (.inl slot)=embedding slot := rfl

omit [Fintype Pool] in
@[simp] theorem placementPartition_inr (embedding : Selected ↪ Pool)
    (slot : {slot : Pool // slot∉Finset.univ.map embedding}) :
    placementPartition embedding (.inr slot)=slot.val := rfl

/-- The full public product channel with a placed score agrees exactly with
the selected signed channel times the integrated unselected background. -/
theorem expectation_placed_product (embedding : Selected ↪ Pool)
    (law : Pool → FiniteDist Color) (score : (Selected → Color) → ℝ)
    (physical : Pool → Color → ℝ) :
    (independent law).expectation (fun word => score (word ∘ embedding)*∏ slot,physical slot (word slot))=
      (independent (fun slot => law (embedding slot))).expectation
        (fun word => score word*∏ slot,physical (embedding slot) (word slot))*
      ∏ slot : {slot : Pool // slot∉Finset.univ.map embedding},(law slot.val).expectation (physical slot.val) := by
  simpa only [placementPartition_inl,placementPartition_inr,Function.comp_def] using
    expectation_split_product (placementPartition embedding) law score physical

/-- The complete two-pool statistic is the uniform average of the literal
placed signed channels, with both distinct-index normalizers exact. -/
theorem twoPoolStatistic_physical_expectation
    {PS BS PP BP : Type*} [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP]
    (law : PP ⊕ BP → FiniteDist Color) (score : (PS ⊕ BS → Color) → ℝ)
    (physical : PP ⊕ BP → Color → ℝ) :
    (independent law).expectation (fun word => twoPoolStatistic score word*∏ slot,physical slot (word slot))=
    (Fintype.card ((PS ↪ PP) × (BS ↪ BP)) : ℝ)⁻¹*
      ∑ choice : (PS ↪ PP) × (BS ↪ BP),
        (independent (fun slot => law ((choice.1.sumMap choice.2) slot))).expectation
          (fun word => score word*∏ slot,physical ((choice.1.sumMap choice.2) slot) (word slot))*
        ∏ slot : {slot : PP ⊕ BP // slot∉Finset.univ.map (choice.1.sumMap choice.2)},
          (law slot.val).expectation (physical slot.val) := by
  have hcard : (Fintype.card ((PS ↪ PP) × (BS ↪ BP)) : ℝ)=
      (Fintype.card PP).descFactorial (Fintype.card PS)*( (Fintype.card BP).descFactorial (Fintype.card BS) : ℝ) := by
    simp [Fintype.card_prod,Fintype.card_embedding_eq]
  rw [hcard]
  simp only [twoPoolStatistic,div_eq_mul_inv,Finset.sum_mul]
  rw [expectation_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro choice _
  have hp : (fun word : PP ⊕ BP → Color =>
      placedKernel score (choice.1.sumMap choice.2) word *
        ((Fintype.card PP).descFactorial (Fintype.card PS)*( (Fintype.card BP).descFactorial (Fintype.card BS) : ℝ))⁻¹ *
          ∏ slot,physical slot (word slot))=
      fun word => (placedKernel score (choice.1.sumMap choice.2) word*∏ slot,physical slot (word slot))*
        ((Fintype.card PP).descFactorial (Fintype.card PS)*( (Fintype.card BP).descFactorial (Fintype.card BS) : ℝ))⁻¹ := by
    funext word; ring
  rw [hp,expectation_mul_const]
  simp only [placedKernel]
  rw [expectation_placed_product]
  ring

end
end AFT.FiniteDist

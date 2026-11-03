import AFT.CompatibleFibers
import AFT.TwoPoolCollisionCounting

/-! # Actual canonical statistics on two independent pools -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

local instance {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _


section Compatible

variable {Slot Pool Color Copy : Type*}
  [Fintype Slot] [Fintype Pool] [Fintype Color] [Fintype Copy]

omit [Fintype Copy] [Fintype Pool] in
theorem placedKernel_canonical_compatible (reference : Pool → FiniteDist Color)
    (inputReference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical inputReference Finset.univ kernel)
    (placement : Slot ↪ Pool) (hcompatible : ∀ slot, reference (placement slot) = inputReference slot) :
    Hoeffding.Canonical reference (Finset.univ.map placement) (placedKernel kernel placement) := by
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
    simp only [placedKernel, hword, hcompatible]
    exact hcanonical.2 slot (Finset.mem_univ _) (word ∘ placement)

/-- A genuinely singleton coordinate integrates to zero under its own pool law. -/
theorem pattern_expectation_zero_of_singleton_compatible (reference : Pool → FiniteDist Color)
    (inputReference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical inputReference Finset.univ kernel)
    (pattern : Copy → Slot ↪ Pool)
    (hcompatible : ∀ copy slot, reference (pattern copy slot) = inputReference slot)
    (singleCopy : Copy) (singleSlot : Slot)
    (hsingle : ∀ copy, copy ≠ singleCopy → ∀ slot,
      pattern copy slot ≠ pattern singleCopy singleSlot) :
    (FiniteDist.independent reference).expectation (patternProduct kernel pattern) = 0 := by
  let label := pattern singleCopy singleSlot
  let remainder (word : Pool → Color) :=
    ∏ copy ∈ Finset.univ.erase singleCopy, placedKernel kernel (pattern copy) word
  have hcentered := (placedKernel_canonical_compatible reference inputReference kernel hcanonical
    (pattern singleCopy) (hcompatible singleCopy)).2 label
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
  have h := Hoeffding.orthogonal_of_centered reference (Finset.univ.erase label)
    label (by simp) (placedKernel kernel (pattern singleCopy)) remainder hcentered hdepends
  have heq : patternProduct kernel pattern =
      (fun word => placedKernel kernel (pattern singleCopy) word * remainder word) := by
    funext word
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ singleCopy)).symm
  rw [heq]
  exact h

theorem noSingleton_of_expectation_ne_zero_compatible (reference : Pool → FiniteDist Color)
    (inputReference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical inputReference Finset.univ kernel)
    (pattern : Copy → Slot ↪ Pool)
    (hcompatible : ∀ copy slot, reference (pattern copy slot) = inputReference slot)
    (hne : (FiniteDist.independent reference).expectation (patternProduct kernel pattern) ≠ 0) :
    NoSingleton pattern := by
  by_contra h
  simp only [NoSingleton, not_forall, not_exists, not_and] at h
  obtain ⟨copy, slot, hsingle⟩ := h
  apply hne
  apply pattern_expectation_zero_of_singleton_compatible reference inputReference kernel hcanonical
    pattern hcompatible copy slot
  intro otherCopy hcopy otherSlot
  exact hsingle otherCopy otherSlot hcopy

end Compatible

section TwoPools

variable {PS BS PP BP Color Copy : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color] [Fintype Copy]

/-- Each copy chooses its actual primary and body indices independently. -/
def sumPattern (pattern : (Copy → PS ↪ PP) × (Copy → BS ↪ BP)) : Copy → (PS ⊕ BS) ↪ (PP ⊕ BP) :=
  fun copy => (pattern.1 copy).sumMap (pattern.2 copy)

omit [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color] [Fintype Copy] in
theorem sumPattern_noSingleton (pattern : (Copy → PS ↪ PP) × (Copy → BS ↪ BP)) :
    NoSingleton (sumPattern pattern) ↔ NoSingleton pattern.1 ∧ NoSingleton pattern.2 := by
  constructor
  · intro h
    constructor
    · intro copy slot
      obtain ⟨other, otherSlot, hother, heq⟩ := h copy (Sum.inl slot)
      cases otherSlot with
      | inl otherSlot => exact ⟨other, otherSlot, hother, Sum.inl.inj heq⟩
      | inr otherSlot => cases heq
    · intro copy slot
      obtain ⟨other, otherSlot, hother, heq⟩ := h copy (Sum.inr slot)
      cases otherSlot with
      | inl otherSlot => cases heq
      | inr otherSlot => exact ⟨other, otherSlot, hother, Sum.inr.inj heq⟩
  · rintro ⟨hp, hb⟩ copy (slot | slot)
    · obtain ⟨other, otherSlot, hother, heq⟩ := hp copy slot
      exact ⟨other, Sum.inl otherSlot, hother, congrArg Sum.inl heq⟩
    · obtain ⟨other, otherSlot, hother, heq⟩ := hb copy slot
      exact ⟨other, Sum.inr otherSlot, hother, congrArg Sum.inr heq⟩

omit [Fintype Copy] in
/-- Ordered U-statistic with both exact distinct-index normalizers. -/
def twoPoolStatistic (kernel : ((PS ⊕ BS) → Color) → ℝ) (word : (PP ⊕ BP) → Color) : ℝ :=
  (∑ placement : (PS ↪ PP) × (BS ↪ BP), placedKernel kernel (placement.1.sumMap placement.2) word) /
    (((Fintype.card PP).descFactorial (Fintype.card PS) : ℝ) *
      ((Fintype.card BP).descFactorial (Fintype.card BS) : ℝ))

omit [Fintype Copy] in
theorem twoPoolStatistic_moment_expansion (primary body : FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ) (power : ℕ) :
    (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => twoPoolStatistic kernel word ^ power) =
      (∑ pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP),
        (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
          (patternProduct kernel (sumPattern pattern))) /
      (((Fintype.card PP).descFactorial (Fintype.card PS) : ℝ) *
        ((Fintype.card BP).descFactorial (Fintype.card BS) : ℝ)) ^ power := by
  unfold twoPoolStatistic FiniteDist.expectation patternProduct
  simp only [div_pow, Fintype.sum_pow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he := (Equiv.arrowProdEquivProdArrow (Fin power) (fun _ => PS ↪ PP) (fun _ => BS ↪ BP)).symm.sum_comp
    (fun pattern : Fin power → (PS ↪ PP) × (BS ↪ BP) =>
      ∑ word, (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).weight word *
        ∏ copy, placedKernel kernel ((pattern copy).1.sumMap (pattern copy).2) word)
  exact he.symm

omit [Fintype Copy] in
theorem twoPoolStatistic_moment_surviving_expansion (primary body : FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) Finset.univ kernel)
    (power : ℕ) :
    (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => twoPoolStatistic kernel word ^ power) =
      (∑ pattern ∈ Finset.univ.filter (fun pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP) =>
          NoSingleton pattern.1 ∧ NoSingleton pattern.2),
        (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
          (patternProduct kernel (sumPattern pattern))) /
      (((Fintype.card PP).descFactorial (Fintype.card PS) : ℝ) *
        ((Fintype.card BP).descFactorial (Fintype.card BS) : ℝ)) ^ power := by
  rw [twoPoolStatistic_moment_expansion]
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro pattern _ hnot
  by_contra hne
  apply hnot
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  apply (sumPattern_noSingleton pattern).mp
  apply noSingleton_of_expectation_ne_zero_compatible _ _ kernel hcanonical _ _ hne
  intro copy slot
  cases slot <;> rfl

end TwoPools

end

end AFT.CanonicalMoments

import CurrentAFT.PublicAuxiliaryFubini

/-! # Exact product Fubini for independent public charts and hidden scalars -/

namespace CurrentAFT.FiniteProductFubini

open AFT PublicAuxiliaryFubini
open scoped BigOperators Classical

noncomputable section

theorem two_products {Index First Second : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype First] [Fintype Second]
    (first : Index → FiniteDist First) (second : Index → FiniteDist Second)
    (factor : Index → First → Second → ℝ) :
    (FiniteDist.independent first).expectation (fun left =>
      (FiniteDist.independent second).expectation (fun right =>
        ∏ index, factor index (left index) (right index))) =
      ∏ index, (first index).expectation (fun left => (second index).expectation (factor index left)) := by
  rw [FiniteDist.expectation_comm]
  trans (FiniteDist.independent second).expectation (fun right =>
    ∏ index, (first index).expectation (fun left => factor index left (right index)))
  · apply congrArg (FiniteDist.expectation (FiniteDist.independent second))
    funext right
    exact independent_product first (fun index left => factor index left (right index))
  · trans ∏ index, (second index).expectation (fun right =>
      (first index).expectation (fun left => factor index left right))
    · exact independent_product second (fun index right =>
        (first index).expectation (fun left => factor index left right))
    · apply Finset.prod_congr rfl
      intro index _
      exact FiniteDist.expectation_comm _ _ _

theorem three_products {Index Public First Second : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Public] [Fintype First] [Fintype Second]
    (publicLaw : Index → FiniteDist Public) (first : Index → FiniteDist First)
    (second : Index → FiniteDist Second) (factor : Index → Public → First → Second → ℝ) :
    (FiniteDist.independent publicLaw).expectation (fun charts =>
      (FiniteDist.independent first).expectation (fun left =>
        (FiniteDist.independent second).expectation (fun right =>
          ∏ index, factor index (charts index) (left index) (right index)))) =
      ∏ index, (publicLaw index).expectation (fun chart =>
        (first index).expectation (fun left => (second index).expectation (factor index chart left))) := by
  trans (FiniteDist.independent publicLaw).expectation (fun charts =>
    ∏ index, (first index).expectation (fun left =>
      (second index).expectation (factor index (charts index) left)))
  · apply congrArg (FiniteDist.expectation (FiniteDist.independent publicLaw))
    funext charts
    exact two_products first second (fun index => factor index (charts index))
  · exact independent_product publicLaw (fun index chart =>
      (first index).expectation (fun left => (second index).expectation (factor index chart left)))

theorem product_delta {Index Color : Type*} [Fintype Index] (first second : Index → Color) :
    (∏ index, if first index = second index then (1 : ℝ) else 0) =
      if first = second then 1 else 0 := by
  rw [Finset.prod_ite_zero]
  have heq : (∀ index ∈ (Finset.univ : Finset Index), first index = second index) ↔ first = second := by
    simp only [Finset.mem_univ, forall_true_left]
    exact funext_iff.symm
  simp only [heq, Finset.prod_const_one]

theorem block_delta {Index Color : Type*} [Fintype Index]
    (Slots : Index → Type*) (first second : Sigma Slots → Color) :
    (if first = second then (1 : ℝ) else 0) =
      ∏ index, if (fun slot => first ⟨index, slot⟩) = (fun slot => second ⟨index, slot⟩) then 1 else 0 := by
  rw [Finset.prod_ite_zero]
  have heq : (∀ index ∈ (Finset.univ : Finset Index),
      (fun slot => first ⟨index, slot⟩) = (fun slot => second ⟨index, slot⟩)) ↔ first = second := by
    simp only [Finset.mem_univ, forall_true_left]
    constructor
    · intro h
      funext point
      exact congrFun (h point.1) point.2
    · rintro rfl
      exact fun _ => rfl
  simp only [heq, Finset.prod_const_one]

end
end CurrentAFT.FiniteProductFubini

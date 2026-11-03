import CurrentAFT.CycleRootExpansion
import AFT.RootPolynomialCutoff

/-!
# Actual closed-cycle polynomial response and exact root-order cutoff

Only the generic finite-polynomial support lemma from the historical tree
is reused. The source law, reference, canonical components and singleton
cancellation here are the current protected closed cycle.
-/

namespace CurrentAFT.CycleRootPolynomial

open AFT CycleRootExpansion RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance currentModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩
attribute [local irreducible] Parameters.base Parameters.bodySize rootLaw rootReference

variable {Output : Type*}

def polynomialComponent (security : ℕ) (selected : Finset (Vertex security))
    (polynomial : Vertex security → Root security → MvPolynomial Output ℝ) : MvPolynomial Output ℝ :=
  actualComponent security selected (fun roots => ∏ index, polynomial index (roots index))

/-- Every tagged root must occur in a positive-degree output factor. This
is a coefficient identity for the actual complete joint root component. -/
theorem polynomialComponent_hasOrder (security : ℕ) (selected : Finset (Vertex security))
    (polynomial : Vertex security → Root security → MvPolynomial Output ℝ)
    (hconstant : ∀ index root, MvPolynomial.constantCoeff (polynomial index root) = 1) :
    HasOrder (fun _ : Output => 1) selected.card (polynomialComponent security selected polynomial) :=
  canonical_polynomial_product_hasOrder _ _ _
    (actualComponent_canonical security selected) polynomial hconstant

theorem polynomialComponent_truncate_zero (security order : ℕ) (selected : Finset (Vertex security))
    (polynomial : Vertex security → Root security → MvPolynomial Output ℝ)
    (hconstant : ∀ index root, MvPolynomial.constantCoeff (polynomial index root) = 1)
    (hlarge : order < selected.card) :
    truncate (fun _ : Output => 1) order (polynomialComponent security selected polynomial) = 0 :=
  truncate_of_hasOrder _ order _ (hasOrder_mono _ (order + 1) selected.card _
    (polynomialComponent_hasOrder security selected polynomial hconstant) hlarge)

def polynomialDefect (security : ℕ)
    (polynomial : Vertex security → Root security → MvPolynomial Output ℝ) : MvPolynomial Output ℝ :=
  expectationLinear (rootLaw security) (fun roots => ∏ index, polynomial index (roots index)) -
    expectationLinear (FiniteDist.independent (fun _ : Vertex security => rootReference security))
      (fun roots => ∏ index, polynomial index (roots index))

theorem polynomialDefect_expansion (security : ℕ)
    (polynomial : Vertex security → Root security → MvPolynomial Output ℝ) :
    polynomialDefect security polynomial =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Vertex security))).filter
          (fun selected => 2 ≤ selected.card), polynomialComponent security selected polynomial := by
  have h := LinearMap.congr_fun (actual_response_defect (Value := MvPolynomial Output ℝ) security)
    (fun roots => ∏ index, polynomial index (roots index))
  simpa only [polynomialDefect, polynomialComponent, LinearMap.sub_apply, LinearMap.sum_apply] using h

theorem polynomialDefect_hasOrder (security : ℕ)
    (polynomial : Vertex security → Root security → MvPolynomial Output ℝ)
    (hconstant : ∀ index root, MvPolynomial.constantCoeff (polynomial index root) = 1) :
    HasOrder (fun _ : Output => 1) 2 (polynomialDefect security polynomial) := by
  rw [polynomialDefect_expansion]
  apply hasOrder_sum
  intro selected hselected
  exact hasOrder_mono _ 2 selected.card _
    (polynomialComponent_hasOrder security selected polynomial hconstant)
    (Finset.mem_filter.mp hselected).2

/-- Exact finite cutoff: no root subset of size greater than the output
order contributes, and no scalar or singleton term is hidden in the defect. -/
theorem polynomialDefect_truncated_sources (security order : ℕ)
    (polynomial : Vertex security → Root security → MvPolynomial Output ℝ)
    (hconstant : ∀ index root, MvPolynomial.constantCoeff (polynomial index root) = 1) :
    truncate (fun _ : Output => 1) order (polynomialDefect security polynomial) =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Vertex security))).filter
          (fun selected => 2 ≤ selected.card ∧ selected.card ≤ order),
        truncate (fun _ : Output => 1) order (polynomialComponent security selected polynomial) := by
  rw [polynomialDefect_expansion, truncate_finset_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro selected _
  by_cases hlow : 2 ≤ selected.card
  · rw [if_pos hlow]
    by_cases hhigh : selected.card ≤ order
    · rw [if_pos ⟨hlow, hhigh⟩]
    · rw [if_neg (fun h => hhigh h.2)]
      exact polynomialComponent_truncate_zero security order selected polynomial hconstant
        (Nat.lt_of_not_ge hhigh)
  · rw [if_neg hlow, if_neg (fun h => hlow h.1)]

end
end CurrentAFT.CycleRootPolynomial

import AFT.RepresentedFiniteKernel
import AFT.RepresentedTruncation

/-! # Literal joint-kernel coordinate counts equal formal input order -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*}

theorem finiteControlCount_eq_sum (seeds : List (InputSeed Color)) :
    finiteControlCount seeds = (seeds.map fun seed => seed.primaryOrder + seed.bodyOrder).sum := by
  induction seeds with
  | nil => simp [finiteControlCount, ControlProductSlot]
  | cons seed rest ih =>
    change Fintype.card (Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest) = _
    simp only [Fintype.card_sum, Fintype.card_fin, List.map_cons, List.sum_cons]
    rw [show Fintype.card (ControlProductSlot rest) = _ from ih]

theorem monomialOccurrences_order (powers : InputSeed Color →₀ ℕ) :
    finiteControlCount (monomialOccurrences powers) =
      weightedOrder (fun seed => seed.primaryOrder + seed.bodyOrder) powers := by
  rw [finiteControlCount_eq_sum]
  unfold monomialOccurrences weightedOrder Finsupp.sum
  rw [List.map_flatMap]
  have hh (seeds : List (InputSeed Color)) :
      (seeds.flatMap fun seed => List.replicate (powers seed) (seed.primaryOrder + seed.bodyOrder)).sum =
        (seeds.map fun seed => powers seed * (seed.primaryOrder + seed.bodyOrder)).sum := by
    induction seeds with
    | nil => simp
    | cons seed seeds ih => simp [List.flatMap_cons, ih]
  simpa using hh powers.support.toList

theorem truncated_monomial_order_le (table : Table (InputSeed Color)) (cutoff : ℕ)
    (powers : InputSeed Color →₀ ℕ)
    (hp : powers ∈ (truncate (fun seed => seed.primaryOrder + seed.bodyOrder) cutoff table).support) :
    finiteControlCount (monomialOccurrences powers) ≤ cutoff := by
  rw [monomialOccurrences_order]
  exact (Finset.mem_filter.mp hp).2

theorem positive_monomial_order (table : Table (InputSeed Color))
    (h : HasOrder (fun seed => seed.primaryOrder + seed.bodyOrder) 1 table)
    (powers : InputSeed Color →₀ ℕ) (hp : powers ∈ table.support) :
    0 < finiteControlCount (monomialOccurrences powers) := by
  rw [monomialOccurrences_order]
  by_contra hn
  have hz := h powers (by omega)
  exact (Finsupp.mem_support_iff.mp hp) hz

end
end AFT.RepresentedPolynomial

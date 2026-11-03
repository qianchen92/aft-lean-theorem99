import AFT.RootSlice

/-!
# Exact multi-coordinate marginals of the integer root slice

The selected coordinates are a literal prefix of the full independent
product, and the law is conditioned on the full integer sum. The numerator
below is derived by the append equivalence of those actual finite spaces.
-/

namespace AFT.RootSlice

open scoped BigOperators Classical

noncomputable section

local instance (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {α : Type*} [Fintype α]

def sumProbability (source : FiniteDist α) (score : α → ℤ) (count : ℕ) (target : ℤ) : ℝ :=
  probability (fun _ : Fin count => source) score target

def prefixLaw (source : FiniteDist α) (score : α → ℤ) (selected remaining : ℕ)
    (h : 0 < sumProbability source score (selected + remaining) 0) :
    FiniteDist (Fin selected → α) :=
  (law (fun _ : Fin (selected + remaining) => source) score 0 h).map
    (fun x i => x (Fin.castAdd remaining i))

theorem sumProbability_append (source : FiniteDist α) (score : α → ℤ)
    (selected remaining : ℕ) (target : ℤ) :
    sumProbability source score (selected + remaining) target =
      ∑ x : Fin selected → α, (∏ i, source.weight (x i)) *
        sumProbability source score remaining (target - integerSum score x) := by
  classical
  unfold sumProbability probability FiniteDist.eventMass FiniteDist.independent
  dsimp only
  have hreindex := (Fin.appendEquiv (α := α) selected remaining).sum_comp
    (fun x : Fin (selected + remaining) → α => if integerSum score x = target then
      ∏ i, source.weight (x i) else 0)
  trans ∑ uv : (Fin selected → α) × (Fin remaining → α),
    if integerSum score ((Fin.appendEquiv selected remaining) uv) = target then
      ∏ i, source.weight ((Fin.appendEquiv selected remaining) uv i) else 0
  · convert hreindex.symm using 1
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> rfl
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hsum : integerSum score ((Fin.appendEquiv selected remaining) (x, y)) =
      integerSum score x + integerSum score y := by
    change integerSum score (Fin.append x y) = _
    unfold integerSum
    rw [Fin.sum_univ_add]
    simp
  have hprod : (∏ i, source.weight (Fin.append x y i)) =
      (∏ i, source.weight (x i)) * ∏ i, source.weight (y i) := by
    rw [Fin.prod_univ_add]
    simp
  by_cases hy : integerSum score y = target - integerSum score x
  · have ht : integerSum score ((Fin.appendEquiv selected remaining) (x, y)) = target := by omega
    simp only [if_pos ht, if_pos hy, Fin.appendEquiv_apply, hprod]
  · have ht : integerSum score ((Fin.appendEquiv selected remaining) (x, y)) ≠ target := by omega
    simp only [if_neg ht, if_neg hy, mul_zero]

theorem prefixLaw_weight (source : FiniteDist α) (score : α → ℤ) (selected remaining : ℕ)
    (h : 0 < sumProbability source score (selected + remaining) 0) (x : Fin selected → α) :
    (prefixLaw source score selected remaining h).weight x =
      (∏ i, source.weight (x i)) * sumProbability source score remaining (-integerSum score x) /
        sumProbability source score (selected + remaining) 0 := by
  classical
  unfold prefixLaw
  rw [FiniteDist.map_weight]
  have hreindex := (Fin.appendEquiv (α := α) selected remaining).sum_comp
    (fun a : Fin (selected + remaining) → α => if (fun i => a (Fin.castAdd remaining i)) = x then
      (law (fun _ : Fin (selected + remaining) => source) score 0 h).weight a else 0)
  trans ∑ uv : (Fin selected → α) × (Fin remaining → α),
    if (fun i => (Fin.appendEquiv selected remaining) uv (Fin.castAdd remaining i)) = x then
      (law (fun _ : Fin (selected + remaining) => source) score 0 h).weight
        ((Fin.appendEquiv selected remaining) uv) else 0
  · convert hreindex.symm using 1
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> rfl
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hrestrict (u : Fin selected → α) (v : Fin remaining → α) :
      (fun i => (Fin.appendEquiv selected remaining) (u, v) (Fin.castAdd remaining i)) = u := by
    funext i
    simp
  simp only [hrestrict]
  have hsingle (y : Fin remaining → α) :
      (∑ u : Fin selected → α, if u = x then
        (law (fun _ : Fin (selected + remaining) => source) score 0 h).weight
          (Fin.appendEquiv selected remaining (u, y)) else 0) =
        (law (fun _ : Fin (selected + remaining) => source) score 0 h).weight
          (Fin.appendEquiv selected remaining (x, y)) := by simp
  simp only [hsingle]
  unfold sumProbability probability FiniteDist.eventMass FiniteDist.independent
  dsimp only
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  have hsum : integerSum score ((Fin.appendEquiv selected remaining) (x, y)) =
      integerSum score x + integerSum score y := by
    change integerSum score (Fin.append x y) = _
    unfold integerSum
    rw [Fin.sum_univ_add]
    simp
  have hprod : (∏ i, source.weight (Fin.append x y i)) =
      (∏ i, source.weight (x i)) * ∏ i, source.weight (y i) := by
    rw [Fin.prod_univ_add]
    simp
  simp only [law, FiniteDist.condition, FiniteDist.independent, FiniteDist.eventMass]
  by_cases hy : integerSum score y = -integerSum score x
  · have ht : integerSum score ((Fin.appendEquiv selected remaining) (x, y)) = 0 := by omega
    simp only [if_pos ht, if_pos hy, Fin.appendEquiv_apply, hprod]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> rfl
  · have ht : integerSum score ((Fin.appendEquiv selected remaining) (x, y)) ≠ 0 := by omega
    simp only [if_neg ht, if_neg hy, mul_zero, zero_div]

/-- The actual first-coordinate law of a population root slice. -/
def marginalLaw (source : FiniteDist α) (score : α → ℤ) (population : ℕ)
    (hn : 0 < population) (h : 0 < sumProbability source score population 0) : FiniteDist α :=
  (prefixLaw source score 1 (population - 1)
    (by have heq : 1 + (population - 1) = population := by omega
        simpa only [heq] using h)).map (Equiv.funUnique (Fin 1) α)

theorem marginalLaw_weight (source : FiniteDist α) (score : α → ℤ) (population : ℕ)
    (hn : 0 < population) (h : 0 < sumProbability source score population 0) (a : α) :
    (marginalLaw source score population hn h).weight a =
      source.weight a * sumProbability source score (population - 1) (-score a) /
        sumProbability source score population 0 := by
  unfold marginalLaw
  rw [FiniteDist.map_equiv_weight, prefixLaw_weight]
  have heq : 1 + (population - 1) = population := by omega
  simp [Equiv.funUnique, Equiv.piUnique, integerSum, heq]

/-- The exact quotient used in the root ANOVA analysis. Both the joint law
and every factor of the reference law are actual marginals of the same
conditioned population. -/
theorem prefix_density_ratio (source : FiniteDist α) (score : α → ℤ)
    (selected remaining : ℕ) (hk : 0 < selected)
    (h : 0 < sumProbability source score (selected + remaining) 0)
    (hsource : ∀ a, 0 < source.weight a)
    (hother : ∀ a, 0 < sumProbability source score (selected + remaining - 1) (-score a))
    (x : Fin selected → α) :
    (prefixLaw source score selected remaining h).weight x /
        (FiniteDist.independent (fun _ : Fin selected =>
          marginalLaw source score (selected + remaining) (by omega) h)).weight x =
      sumProbability source score remaining (-integerSum score x) *
          sumProbability source score (selected + remaining) 0 ^ (selected - 1) /
        ∏ i, sumProbability source score (selected + remaining - 1) (-score (x i)) := by
  rw [prefixLaw_weight]
  change _ / (∏ i, (marginalLaw source score (selected + remaining) _ h).weight (x i)) = _
  simp_rw [marginalLaw_weight]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hsrc : (∏ i, source.weight (x i)) ≠ 0 :=
    (Finset.prod_pos fun i _ => hsource (x i)).ne'
  have hden : (∏ i, sumProbability source score (selected + remaining - 1) (-score (x i))) ≠ 0 :=
    (Finset.prod_pos fun i _ => hother (x i)).ne'
  have hp : sumProbability source score (selected + remaining) 0 ^ selected =
      sumProbability source score (selected + remaining) 0 *
        sumProbability source score (selected + remaining) 0 ^ (selected - 1) := by
    simpa only [Nat.sub_add_cancel hk, mul_comm] using
      (pow_succ (sumProbability source score (selected + remaining) 0) (selected - 1))
  rw [hp]
  field_simp


end

end AFT.RootSlice

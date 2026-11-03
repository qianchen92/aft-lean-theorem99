import AFT.Histogram

/-!
# Exact finite product orthogonality and histogram isometry

The sums in this file are over the actual finite product space. No limiting
Poisson experiment or infinite-population normalization is used.
-/

namespace AFT

open scoped BigOperators
open scoped Classical

namespace FiniteDist

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

/-- The product of a finite, possibly nonidentical family of laws. -/
noncomputable def independent [DecidableEq ι] (p : ι → FiniteDist α) : FiniteDist (ι → α) where
  weight x := ∏ i, (p i).weight (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (p i).nonneg (x i)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [sum_one, Finset.prod_const_one]

/-- Real expectation, including signed functions. -/
noncomputable def expectation (p : FiniteDist α) (f : α → ℝ) : ℝ :=
  ∑ x, p.weight x * f x

/-- Squared `L²` norm with respect to the specified law. -/
noncomputable def l2Sq (p : FiniteDist α) (f : α → ℝ) : ℝ :=
  p.expectation fun x => f x ^ 2

theorem l2Sq_nonneg (p : FiniteDist α) (f : α → ℝ) : 0 ≤ p.l2Sq f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg _)

theorem expectation_map (p : FiniteDist α) (g : α → β) (f : β → ℝ) :
    (p.map g).expectation f = p.expectation (f ∘ g) := by
  classical
  unfold expectation
  simp only [map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

/-- Every function of the histogram has exactly the same norm before and
after passing to the histogram law. This applies to signed likelihoods. -/
theorem l2Sq_map (p : FiniteDist α) (g : α → β) (f : β → ℝ) :
    (p.map g).l2Sq f = p.l2Sq (f ∘ g) := by
  exact p.expectation_map g (fun y => f y ^ 2)

theorem expectation_independent_split (p : ι → FiniteDist α)
    (i : ι) (f : (ι → α) → ℝ) :
    (independent p).expectation f =
      ∑ y : {j : ι // j ≠ i} → α,
        (∏ j : {j : ι // j ≠ i}, (p j).weight (y j)) *
          ∑ a, (p i).weight a * f ((Equiv.funSplitAt i α).symm (a, y)) := by
  classical
  unfold expectation independent
  rw [← (Equiv.funSplitAt i α).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hp : (∏ j, (p j).weight ((Equiv.funSplitAt i α).symm (a, y) j)) =
      (p i).weight a * ∏ j : {j : ι // j ≠ i}, (p j).weight (y j) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    apply congrArg₂ (· * ·)
    · simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · apply Finset.prod_congr rfl
      intro j _
      simp [Equiv.funSplitAt, Equiv.piSplitAt, j.property]
  change (∏ j, (p j).weight ((Equiv.funSplitAt i α).symm (a, y) j)) * _ = _
  rw [hp]
  ring

end FiniteDist

namespace Hoeffding

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- A function uses only coordinates in `S`. -/
def DependsOn (S : Finset ι) (f : (ι → α) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

/-- Conditional mean zero in one coordinate, with all others fixed. -/
def CenteredAt (p : ι → FiniteDist α) (i : ι) (f : (ι → α) → ℝ) : Prop :=
  ∀ x, ∑ a, (p i).weight a * f (Function.update x i a) = 0

/-- The actual canonicality condition for a finite-product kernel. -/
def Canonical (p : ι → FiniteDist α) (S : Finset ι) (f : (ι → α) → ℝ) : Prop :=
  DependsOn S f ∧ ∀ i ∈ S, CenteredAt p i f

/-- Integrating a coordinate appearing in just one factor annihilates the
inner product. This is the exact finite-population orthogonality argument. -/
theorem orthogonal_of_centered (p : ι → FiniteDist α) (S : Finset ι)
    (i : ι) (hi : i ∉ S) (f g : (ι → α) → ℝ)
    (hf : CenteredAt p i f) (hg : DependsOn S g) :
    (FiniteDist.independent p).expectation (fun x => f x * g x) = 0 := by
  classical
  rw [FiniteDist.expectation_independent_split p i]
  apply Finset.sum_eq_zero
  intro y _
  haveI : Nonempty α := by
    by_contra hn
    haveI : IsEmpty α := not_nonempty_iff.mp hn
    have h := (p i).sum_one
    simp at h
  let x : ι → α := (Equiv.funSplitAt i α).symm (Classical.choice inferInstance, y)
  have hupdate (a : α) :
      (Equiv.funSplitAt i α).symm (a, y) = Function.update x i a := by
    funext j
    by_cases hji : j = i
    · subst j; simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [Equiv.funSplitAt, Equiv.piSplitAt, Function.update, hji, x]
  have hgx (a : α) : g (Function.update x i a) = g x := by
    apply hg
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    exact Function.update_of_ne hji a x
  simp_rw [hupdate, hgx, ← mul_assoc]
  rw [← Finset.sum_mul, hf x, zero_mul, mul_zero]

theorem canonical_orthogonal (p : ι → FiniteDist α) (S T : Finset ι)
    (hne : S ≠ T) (f g : (ι → α) → ℝ)
    (hf : Canonical p S f) (hg : Canonical p T g) :
    (FiniteDist.independent p).expectation (fun x => f x * g x) = 0 := by
  classical
  by_cases hST : S ⊆ T
  · have hTS : ¬ T ⊆ S := fun h => hne (Finset.Subset.antisymm hST h)
    obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
    simpa [mul_comm] using orthogonal_of_centered p S i hiS g f (hg.2 i hiT) hf.1
  · obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
    exact orthogonal_of_centered p T i hiT f g (hf.2 i hiS) hg.1

/-- Exact Pythagoras for an arbitrary finite collection of canonical kernels
on distinct coordinate sets. The index collection may contain every subset. -/
theorem canonical_sum_l2Sq (p : ι → FiniteDist α) (sets : Finset (Finset ι))
    (kernels : Finset ι → (ι → α) → ℝ)
    (h : ∀ S ∈ sets, Canonical p S (kernels S)) :
    (FiniteDist.independent p).l2Sq (fun x => ∑ S ∈ sets, kernels S x) =
      ∑ S ∈ sets, (FiniteDist.independent p).l2Sq (kernels S) := by
  classical
  unfold FiniteDist.l2Sq FiniteDist.expectation
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single S]
  · intro T hT hTS
    have hzero := canonical_orthogonal p S T (Ne.symm hTS)
      (kernels S) (kernels T) (h S hS) (h T hT)
    simpa only [FiniteDist.expectation, mul_assoc] using hzero
  · exact fun hn => False.elim (hn hS)

/-- A normalized distinct-subset average has its exact binomial variance.
The common kernel norm is supplied by relabeling, independently of the
orthogonality established here. -/
theorem canonical_average_l2Sq (p : ι → FiniteDist α)
    (sets : Finset (Finset ι)) (kernels : Finset ι → (ι → α) → ℝ)
    (h : ∀ S ∈ sets, Canonical p S (kernels S))
    (v : ℝ) (hnorm : ∀ S ∈ sets, (FiniteDist.independent p).l2Sq (kernels S) = v) :
    (FiniteDist.independent p).l2Sq
      (fun x => (∑ S ∈ sets, kernels S x) / sets.card) = v / sets.card := by
  classical
  by_cases hn : sets.card = 0
  · simp [hn, FiniteDist.l2Sq, FiniteDist.expectation]
  have hn' : (sets.card : ℝ) ≠ 0 := by exact_mod_cast hn
  have hs := canonical_sum_l2Sq p sets kernels h
  have hh : (∑ S ∈ sets, (FiniteDist.independent p).l2Sq (kernels S)) =
      sets.card * v := by
    calc
      _ = ∑ _S ∈ sets, v := Finset.sum_congr rfl hnorm
      _ = _ := by simp
  rw [hh] at hs
  unfold FiniteDist.l2Sq FiniteDist.expectation at hs ⊢
  simp only [div_pow, ← mul_div_assoc]
  rw [← Finset.sum_div, hs]
  field_simp

/-- Centered density of a point mass relative to the reference color law. -/
noncomputable def centeredAtom (p : FiniteDist α) (source value : α) : ℝ :=
  (if source = value then (p.weight value)⁻¹ else 0) - 1

theorem centeredAtom_mean (p : FiniteDist α) (hp : ∀ a, 0 < p.weight a)
    (source : α) : ∑ a, p.weight a * centeredAtom p source a = 0 := by
  classical
  simp only [centeredAtom, mul_sub, mul_one, Finset.sum_sub_distrib, p.sum_one]
  have hm (a : α) : p.weight a * (if source = a then (p.weight a)⁻¹ else 0) =
      if source = a then (1 : ℝ) else 0 := by
    split_ifs <;> simp [ne_of_gt (hp a)]
  simp_rw [hm]
  simp

/-- The canonical coefficient on a specified subset, computed directly from
an arbitrary signed measure on the labeled product space. -/
noncomputable def densityComponent (p : ι → FiniteDist α)
    (mass : (ι → α) → ℝ) (S : Finset ι) (y : ι → α) : ℝ :=
  ∑ x, mass x * ∏ i ∈ S, centeredAtom (p i) (x i) (y i)

theorem densityComponent_canonical (p : ι → FiniteDist α)
    (hp : ∀ i a, 0 < (p i).weight a) (mass : (ι → α) → ℝ) (S : Finset ι) :
    Canonical p S (densityComponent p mass S) := by
  classical
  constructor
  · intro x y hxy
    unfold densityComponent
    apply Finset.sum_congr rfl
    intro z _
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [hxy i hi]
  · intro i hi y
    simp only [densityComponent, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro x _
    have hprod (a : α) :
        (∏ j ∈ S, centeredAtom (p j) (x j) (Function.update y i a j)) =
          centeredAtom (p i) (x i) a *
            ∏ j ∈ S.erase i, centeredAtom (p j) (x j) (y j) := by
      rw [← Finset.mul_prod_erase _ _ hi]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    simp_rw [hprod]
    have hterm (a : α) : (p i).weight a * (mass x *
        (centeredAtom (p i) (x i) a * ∏ j ∈ S.erase i,
          centeredAtom (p j) (x j) (y j))) =
        (mass x * ∏ j ∈ S.erase i, centeredAtom (p j) (x j) (y j)) *
          ((p i).weight a * centeredAtom (p i) (x i) a) := by ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, centeredAtom_mean (p i) (hp i), mul_zero]

theorem centeredAtom_subset_sum (p : ι → FiniteDist α) (x y : ι → α) :
    (∑ S : Finset ι, ∏ i ∈ S, centeredAtom (p i) (x i) (y i)) =
      if x = y then (∏ i, (p i).weight (y i))⁻¹ else 0 := by
  classical
  rw [← Finset.powerset_univ, ← Finset.prod_one_add]
  simp only [centeredAtom, add_comm (1 : ℝ), sub_add_cancel]
  rw [Fintype.prod_ite_zero]
  simp only [← funext_iff, Finset.prod_inv_distrib]

/-- Exact full Hoeffding expansion of any signed density. The sum includes
all subsets, including degrees near the entire population size. -/
theorem densityComponent_sum (p : ι → FiniteDist α)
    (mass : (ι → α) → ℝ) (y : ι → α) :
    (∑ S : Finset ι, densityComponent p mass S y) =
      mass y / (FiniteDist.independent p).weight y := by
  classical
  unfold densityComponent
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, centeredAtom_subset_sum]
  simp [mul_ite, div_eq_mul_inv, FiniteDist.independent]

/-- Parseval for the full finite signed likelihood, derived from the actual
coefficients and not supplied as an assumption. -/
theorem densityComponent_parseval (p : ι → FiniteDist α)
    (hp : ∀ i a, 0 < (p i).weight a) (mass : (ι → α) → ℝ) :
    (FiniteDist.independent p).l2Sq
        (fun y => mass y / (FiniteDist.independent p).weight y) =
      ∑ S : Finset ι, (FiniteDist.independent p).l2Sq (densityComponent p mass S) := by
  have h := canonical_sum_l2Sq p Finset.univ (densityComponent p mass)
    (fun S _ => densityComponent_canonical p hp mass S)
  simpa only [densityComponent_sum] using h

end Hoeffding

section HistogramIsometry

variable {dimension : ℕ} {Color : Type*} [Fintype Color]

/-- An exchangeable real function factors through the concrete histogram. -/
theorem exchangeable_function_factors
    (f : (Fin dimension → Color) → ℝ)
    (h : ∀ x σ, f (relabel x σ) = f x) :
    ∃ g : Histogram dimension Color → ℝ, f = g ∘ histogram := by
  classical
  let g : Histogram dimension Color → ℝ := fun t =>
    if ht : ∃ x, histogram x = t then f ht.choose else 0
  refine ⟨g, ?_⟩
  funext x
  have hex : ∃ y, histogram y = histogram x := ⟨x, rfl⟩
  simp only [Function.comp_apply, g, dif_pos hex]
  obtain ⟨σ, hσ⟩ := (histogram_eq_iff_relabel hex.choose x).mp hex.choose_spec
  exact (congrArg f hσ).symm.trans (h hex.choose σ)

/-- Exact finite-size histogram isometry for every exchangeable signed
function, with no positivity requirement on that function. -/
theorem exchangeable_histogram_l2Sq
    (p : FiniteDist (Fin dimension → Color))
    (f : (Fin dimension → Color) → ℝ)
    (h : ∀ x σ, f (relabel x σ) = f x) :
    ∃ g : Histogram dimension Color → ℝ,
      f = g ∘ histogram ∧ (p.map histogram).l2Sq g = p.l2Sq f := by
  obtain ⟨g, rfl⟩ := exchangeable_function_factors f h
  exact ⟨g, rfl, p.l2Sq_map histogram g⟩

end HistogramIsometry

end AFT

import AFT.Hoeffding
import AFT.GaussianTail

/-!
# The actual finite root slice

Conditioning is performed on the integer sum, before taking any marginal.
The reference laws below are those marginals themselves. The first canonical
coefficient consequently vanishes exactly. This file does not assume an
asymptotic Gaussian approximation to the convolution masses.
-/

namespace AFT

open scoped BigOperators Classical

noncomputable section

namespace FiniteDist

variable {α : Type*} [Fintype α]

def eventMass (p : FiniteDist α) (event : α → Prop) : ℝ :=
  ∑ x, if event x then p.weight x else 0

theorem eventMass_nonneg (p : FiniteDist α) (event : α → Prop) : 0 ≤ p.eventMass event :=
  Finset.sum_nonneg fun x _ => by split_ifs; exact p.nonneg x; rfl

def condition (p : FiniteDist α) (event : α → Prop) (h : 0 < p.eventMass event) :
    FiniteDist α where
  weight x := (if event x then p.weight x else 0) / p.eventMass event
  nonneg x := div_nonneg (by split_ifs; exact p.nonneg x; rfl) h.le
  sum_one := by rw [← Finset.sum_div]; exact div_self h.ne'

theorem eventMass_positive_of_atom (p : FiniteDist α) (event : α → Prop)
    (x : α) (hx : event x) (hp : 0 < p.weight x) : 0 < p.eventMass event := by
  apply hp.trans_le
  calc
    p.weight x = (if event x then p.weight x else 0) := by rw [if_pos hx]
    _ ≤ ∑ y, if event y then p.weight y else 0 := Finset.single_le_sum (f := fun y => if event y then p.weight y else 0)
      (fun y _ => by dsimp only; split_ifs; exact p.nonneg y; rfl) (Finset.mem_univ x)

def normalize (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (hmass : 0 < ∑ x, weight x) : FiniteDist α where
  weight x := weight x / ∑ y, weight y
  nonneg x := div_nonneg (hweight x) hmass.le
  sum_one := by rw [← Finset.sum_div]; exact div_self hmass.ne'

end FiniteDist

namespace RootSlice

variable {α ι : Type*} [Fintype α] [Fintype ι]

def integerSum (score : α → ℤ) (x : ι → α) : ℤ := ∑ i, score (x i)

def probability (source : ι → FiniteDist α) (score : α → ℤ) (target : ℤ) : ℝ :=
  (FiniteDist.independent source).eventMass (fun x => integerSum score x = target)

def law (source : ι → FiniteDist α) (score : α → ℤ) (target : ℤ)
    (h : 0 < probability source score target) : FiniteDist (ι → α) :=
  (FiniteDist.independent source).condition (fun x => integerSum score x = target) h

def reference (source : ι → FiniteDist α) (score : α → ℤ) (target : ℤ)
    (h : 0 < probability source score target) (i : ι) : FiniteDist α :=
  (law source score target h).map (fun x => x i)

/-- The normalizing event really has positive probability: the all-zero
configuration belongs to it. No conditioning-on-null-event convention occurs. -/
theorem probability_positive (source : ι → FiniteDist α) (score : α → ℤ)
    (zero : α) (hzero : score zero = 0) (hp : ∀ i, 0 < (source i).weight zero) :
    0 < probability source score 0 := by
  apply FiniteDist.eventMass_positive_of_atom _ _ (fun _ => zero)
  · simp [integerSum, hzero]
  · exact Finset.prod_pos fun i _ => hp i

/-- Exact marginal formula: sum over every remaining coordinate in the
integer slice. This is valid for nonidentical source laws as well. -/
theorem reference_weight (source : ι → FiniteDist α) (score : α → ℤ)
    (target : ℤ) (h : 0 < probability source score target) (i : ι) (a : α) :
    (reference source score target h i).weight a =
      (source i).weight a / probability source score target *
        ∑ y : {j : ι // j ≠ i} → α,
          if (∑ j : {j : ι // j ≠ i}, score (y j)) = target - score a
          then ∏ j : {j : ι // j ≠ i}, (source j).weight (y j) else 0 := by
  have hw (b : α) (y : {j : ι // j ≠ i} → α) :
      (law source score target h).weight ((Equiv.funSplitAt i α).symm (b, y)) =
        (if score b + (∑ j, score (y j)) = target
        then (source i).weight b * ∏ j : {j : ι // j ≠ i}, (source j).weight (y j) else 0) /
          probability source score target := by
    have hsum : (∑ j, score ((Equiv.funSplitAt i α).symm (b, y) j)) =
        score b + ∑ j : {j : ι // j ≠ i}, score (y j) := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
      apply congrArg₂ (· + ·)
      · simp [Equiv.funSplitAt, Equiv.piSplitAt]
      · apply Finset.sum_congr rfl
        intro j _
        simp [Equiv.funSplitAt, Equiv.piSplitAt, j.property]
    have hprod : (∏ j, (source j).weight ((Equiv.funSplitAt i α).symm (b, y) j)) =
        (source i).weight b * ∏ j : {j : ι // j ≠ i}, (source j).weight (y j) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
      apply congrArg₂ (· * ·)
      · simp [Equiv.funSplitAt, Equiv.piSplitAt]
      · apply Finset.prod_congr rfl
        intro j _
        simp [Equiv.funSplitAt, Equiv.piSplitAt, j.property]
    simp only [law, FiniteDist.condition, FiniteDist.independent, integerSum, hsum, hprod]
    rfl
  unfold reference
  rw [FiniteDist.map_weight, ← (Equiv.funSplitAt i α).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [hw]
  simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk]
  simp only [dite_true]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_eq_single a]
  rotate_left
  · intro b _ hba
    exact if_neg hba
  · simp
  simp only [ite_true]
  have hevent : score a + (∑ j : {j : ι // j ≠ i}, score (y j)) = target ↔
      (∑ j : {j : ι // j ≠ i}, score (y j)) = target - score a := by omega
  by_cases hh : (∑ j : {j : ι // j ≠ i}, score (y j)) = target - score a
  · simp only [if_pos hh, if_pos (hevent.mpr hh)]
    ring
  · have hn : ¬ score a + (∑ j : {j : ι // j ≠ i}, score (y j)) = target :=
      fun he => hh (hevent.mp he)
    simp only [if_neg hh, if_neg hn, zero_div, mul_zero]

/-- An exact distribution-relative identity behind the zero first root
ANOVA term. It uses the *actual* marginal, not the unconditioned law. -/
theorem first_component_zero (joint : FiniteDist (ι → α)) (i : ι) (y : ι → α)
    (hy : 0 < (joint.map (fun x => x i)).weight (y i)) :
    Hoeffding.densityComponent (fun j => joint.map (fun x => x j))
      joint.weight {i} y = 0 := by
  let marginal := joint.map (fun x => x i)
  have heq := joint.expectation_map (fun x => x i)
    (fun a => Hoeffding.centeredAtom marginal a (y i))
  change marginal.expectation (fun a => Hoeffding.centeredAtom marginal a (y i)) =
    joint.expectation _ at heq
  simp only [Function.comp_def] at heq
  unfold Hoeffding.densityComponent
  simp only [Finset.prod_singleton]
  change joint.expectation (fun x => Hoeffding.centeredAtom marginal (x i) (y i)) = 0
  rw [← heq]
  unfold FiniteDist.expectation Hoeffding.centeredAtom
  simp_rw [mul_sub, mul_ite, mul_zero]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, marginal.sum_one]
  exact sub_eq_zero.mpr (mul_inv_cancel₀ hy.ne')

/-- The precise cutoff principle: a canonical root term with a coordinate
outside the selected physical support has zero contribution, regardless of
the other public coefficient values. -/
theorem canonical_support_cutoff (p : ι → FiniteDist α) (S T : Finset ι)
    (kernel coefficient : (ι → α) → ℝ)
    (hkernel : Hoeffding.Canonical p S kernel)
    (hcoefficient : Hoeffding.DependsOn T coefficient) (h : ¬ S ⊆ T) :
    (FiniteDist.independent p).expectation (fun x => kernel x * coefficient x) = 0 := by
  obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp h
  exact Hoeffding.orthogonal_of_centered p T i hit kernel coefficient
    (hkernel.2 i hi) hcoefficient

/-- The full density relative to the specified product reference. -/
def density (source referenceLaw : ι → FiniteDist α) (score : α → ℤ)
    (target : ℤ) (h : 0 < probability source score target) (x : ι → α) : ℝ :=
  (law source score target h).weight x / (FiniteDist.independent referenceLaw).weight x

/-- Exact full-density square identity from Section 9. It sums the entire
root slice, with no truncation in ANOVA degree. The tilted one-coordinate
weights are `source²/referenceLaw`. -/
theorem density_l2Sq_tilted (source referenceLaw : ι → FiniteDist α) (score : α → ℤ)
    (target : ℤ) (h : 0 < probability source score target)
    (href : ∀ i a, 0 < (referenceLaw i).weight a) :
    (FiniteDist.independent referenceLaw).l2Sq (density source referenceLaw score target h) =
      (∑ x : ι → α, if integerSum score x = target then
        ∏ i, (source i).weight (x i) ^ 2 / (referenceLaw i).weight (x i) else 0) /
          probability source score target ^ 2 := by
  unfold FiniteDist.l2Sq FiniteDist.expectation density
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  have hprod : (∏ i, (referenceLaw i).weight (x i)) ≠ 0 :=
    (Finset.prod_pos fun i _ => href i (x i)).ne'
  simp only [law, FiniteDist.condition, FiniteDist.independent]
  by_cases hx : integerSum score x = target
  · simp only [if_pos hx, Finset.prod_div_distrib, Finset.prod_pow]
    simp only [probability, FiniteDist.independent] at h ⊢
    field_simp [h.ne']
  · simp only [if_neg hx, zero_div, zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- A full product with a likelihood depending on at most `degree` root
coordinates is orthogonal to every higher root ANOVA order. -/
theorem canonical_degree_cutoff (p : ι → FiniteDist α) (S T : Finset ι)
    (kernel coefficient : (ι → α) → ℝ) (degree : ℕ)
    (hkernel : Hoeffding.Canonical p S kernel)
    (hcoefficient : Hoeffding.DependsOn T coefficient)
    (hdegree : T.card ≤ degree) (horder : degree < S.card) :
    (FiniteDist.independent p).expectation (fun x => kernel x * coefficient x) = 0 := by
  apply canonical_support_cutoff p S T kernel coefficient hkernel hcoefficient
  intro hsubset
  exact (not_le_of_gt horder) ((Finset.card_le_card hsubset).trans hdegree)

end RootSlice

end

end AFT

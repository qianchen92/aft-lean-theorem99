import AFT.RootSlice

/-!
# Canonical projections and the root Taylor cutoff

These are the actual Hoeffding projections on a finite product space.
Contraction follows from the full Parseval identity. Polynomial cancellation
is proved monomial by monomial using its variable support.
-/

namespace AFT.Hoeffding

open scoped BigOperators Classical

noncomputable section

variable {α ι : Type*} [Fintype α] [Fintype ι]

def projection (p : ι → FiniteDist α) (S : Finset ι) :
    ((ι → α) → ℝ) →ₗ[ℝ] ((ι → α) → ℝ) where
  toFun f := densityComponent p (fun x : ι → α => (FiniteDist.independent p).weight x * f x) S
  map_add' f g := by
    funext y
    simp only [densityComponent, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  map_smul' scalar f := by
    funext y
    simp only [densityComponent, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

theorem projection_contracts (p : ι → FiniteDist α) (hp : ∀ i a, 0 < (p i).weight a)
    (S : Finset ι) (f : (ι → α) → ℝ) :
    (FiniteDist.independent p).l2Sq (projection p S f) ≤ (FiniteDist.independent p).l2Sq f := by
  have h := densityComponent_parseval p hp (fun x : ι → α => (FiniteDist.independent p).weight x * f x)
  have hf : (fun x : ι → α => (FiniteDist.independent p).weight x * f x /
      (FiniteDist.independent p).weight x) = f := by
    funext x
    have hx : 0 < (FiniteDist.independent p).weight x := Finset.prod_pos fun i _ => hp i (x i)
    field_simp
  rw [hf] at h
  rw [h]
  exact Finset.single_le_sum (fun T _ => FiniteDist.l2Sq_nonneg
    (FiniteDist.independent p)
    (densityComponent p (fun x => (FiniteDist.independent p).weight x * f x) T))
    (Finset.mem_univ S)

theorem centeredAtom_source_mean (p : FiniteDist α) (value : α) (hp : 0 < p.weight value) :
    ∑ source, p.weight source * centeredAtom p source value = 0 := by
  simp only [centeredAtom, mul_sub, mul_one, Finset.sum_sub_distrib, p.sum_one,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact sub_eq_zero.mpr (mul_inv_cancel₀ hp.ne')

theorem projection_vanishes (p : ι → FiniteDist α) (hp : ∀ i a, 0 < (p i).weight a)
    (S T : Finset ι) (f : (ι → α) → ℝ) (hf : DependsOn T f) (hST : ¬ S ⊆ T) :
    projection p S f = 0 := by
  obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
  funext y
  let kernel := fun x : ι → α => ∏ j ∈ S, centeredAtom (p j) (x j) (y j)
  have hk : CenteredAt p i kernel := by
    intro x
    have hprod (a : α) : kernel (Function.update x i a) =
        centeredAtom (p i) a (y i) *
          ∏ j ∈ S.erase i, centeredAtom (p j) (x j) (y j) := by
      dsimp [kernel]
      rw [← Finset.mul_prod_erase _ _ hiS]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    simp_rw [hprod, ← mul_assoc]
    rw [← Finset.sum_mul, centeredAtom_source_mean _ _ (hp i (y i)), zero_mul]
  have hz := orthogonal_of_centered p T i hiT kernel f hk hf
  change ∑ x, ((FiniteDist.independent p).weight x * f x) * kernel x = 0
  convert hz using 1
  unfold FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Every polynomial of degree less than the projection order is killed.
The assertion is about ordinary total degree, so it applies to all Taylor
monomials of the quadratic root exponent. -/
theorem projection_polynomial_zero (p : ι → FiniteDist α) (hp : ∀ i a, 0 < (p i).weight a)
    (S : Finset ι) (value : ι → α → ℝ) (polynomial : MvPolynomial ι ℝ)
    (hdegree : polynomial.totalDegree < S.card) :
    projection p S (fun x : ι → α => MvPolynomial.eval (fun i => value i (x i)) polynomial) = 0 := by
  have hexpand : (fun x : ι → α => MvPolynomial.eval (fun i => value i (x i)) polynomial) =
      ∑ d ∈ polynomial.support, (fun x : ι → α => polynomial.coeff d *
        ∏ i ∈ d.support, value i (x i) ^ d i) := by
    funext x
    simp only [Finset.sum_apply, MvPolynomial.eval_eq]
  rw [hexpand, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply projection_vanishes p hp S d.support
  · intro x y hxy
    change polynomial.coeff d * (∏ i ∈ d.support, value i (x i) ^ d i) =
      polynomial.coeff d * (∏ i ∈ d.support, value i (y i) ^ d i)
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [hxy i hi]
  · have hcard : d.support.card ≤ d.sum (fun _ n => n) := by
      change d.support.card ≤ ∑ i ∈ d.support, d i
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro i hi
      have hn := Finsupp.mem_support_iff.mp hi
      omega
    intro hsubset
    have := (Finset.card_le_card hsubset).trans (hcard.trans (MvPolynomial.le_totalDegree hd))
    omega

/-- An explicit Taylor polynomial of a quadratic exponent has zero full
canonical projection below half the root order. -/
theorem projection_quadratic_taylor_zero (p : ι → FiniteDist α)
    (hp : ∀ i a, 0 < (p i).weight a) (S : Finset ι) (value : ι → α → ℝ)
    (quadratic : MvPolynomial ι ℝ) (hdegree : quadratic.totalDegree ≤ 2)
    (order : ℕ) (horder : ∀ j < order, 2 * j < S.card) :
    projection p S (fun x : ι → α => ∑ j ∈ Finset.range order,
      (MvPolynomial.eval (fun i => value i (x i)) quadratic) ^ j / (j.factorial : ℝ)) = 0 := by
  have heq : (fun x : ι → α => ∑ j ∈ Finset.range order,
      (MvPolynomial.eval (fun i => value i (x i)) quadratic) ^ j / (j.factorial : ℝ)) =
      ∑ j ∈ Finset.range order, (j.factorial : ℝ)⁻¹ •
        (fun x : ι → α => MvPolynomial.eval (fun i => value i (x i)) (quadratic ^ j)) := by
    funext x
    simp [div_eq_mul_inv, mul_comm]
  rw [heq, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [map_smul, projection_polynomial_zero p hp S value (quadratic ^ j)]
  · simp
  · apply (MvPolynomial.totalDegree_pow _ _).trans_lt
    simpa only [Nat.mul_comm] using
      ((Nat.mul_le_mul_right j hdegree).trans_lt (horder j (Finset.mem_range.mp hj)))

theorem real_exp_remainder_bound (x : ℝ) (order : ℕ) :
    |Real.exp x - ∑ j ∈ Finset.range order, x ^ j / (j.factorial : ℝ)| ≤
      |x| ^ order * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) order
  convert h using 1 <;> norm_cast

/-- The complete canonical component of a quadratic exponential is bounded
by its genuine Taylor remainder. Low-degree polynomial terms have already
been annihilated; no bound on those terms is assumed. -/
theorem projection_quadratic_exp_bound (p : ι → FiniteDist α)
    (hp : ∀ i a, 0 < (p i).weight a) (S : Finset ι) (value : ι → α → ℝ)
    (quadratic : MvPolynomial ι ℝ) (hdegree : quadratic.totalDegree ≤ 2)
    (order : ℕ) (horder : ∀ j < order, 2 * j < S.card) :
    (FiniteDist.independent p).l2Sq (projection p S (fun x =>
      Real.exp (MvPolynomial.eval (fun i => value i (x i)) quadratic))) ≤
    (FiniteDist.independent p).expectation (fun x =>
      (|MvPolynomial.eval (fun i => value i (x i)) quadratic| ^ order *
        Real.exp |MvPolynomial.eval (fun i => value i (x i)) quadratic|) ^ 2) := by
  let exponent := fun x : ι → α => MvPolynomial.eval (fun i => value i (x i)) quadratic
  let taylor := fun x : ι → α => ∑ j ∈ Finset.range order, exponent x ^ j / (j.factorial : ℝ)
  have ht : projection p S taylor = 0 :=
    projection_quadratic_taylor_zero p hp S value quadratic hdegree order horder
  have heq : projection p S (fun x => Real.exp (exponent x)) =
      projection p S ((fun x => Real.exp (exponent x)) - taylor) := by
    rw [map_sub, ht, sub_zero]
  change (FiniteDist.independent p).l2Sq (projection p S (fun x => Real.exp (exponent x))) ≤ _
  rw [heq]
  apply (projection_contracts p hp S _).trans
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ ((FiniteDist.independent p).nonneg x)
  have h := real_exp_remainder_bound (exponent x) order
  have hpow := pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa only [sq_abs, Pi.sub_apply] using hpow

/-- The ceiling-half order used in the root ANOVA estimate satisfies the
exact combinatorial inequality required above. -/
theorem ceiling_half_taylor_order (roots j : ℕ) (hj : j < (roots + 1) / 2) :
    2 * j < roots := by omega

end

end AFT.Hoeffding

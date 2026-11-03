import AFT.ProductMoments

/-!
# The quadratic exponent in the root marginal density

The manuscript's pair and diagonal terms simplify exactly to
`sum u_i² / (2 (N-1)) - (sum u_i)² / (2 (N-k))`.
This file constructs that polynomial and proves its full canonical
projection bound from the coordinate exponential-square moments.
-/

namespace AFT.RootSlice

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def quadraticExponent (population : ℝ) : MvPolynomial ι ℝ :=
  (1 / (2 * (population - 1))) • (∑ i, (MvPolynomial.X i : MvPolynomial ι ℝ) ^ 2) -
    (1 / (2 * (population - Fintype.card ι))) •
      (∑ i, (MvPolynomial.X i : MvPolynomial ι ℝ)) ^ 2

theorem quadraticExponent_degree (population : ℝ) :
    (quadraticExponent (ι := ι) population).totalDegree ≤ 2 := by
  have hlinear : (∑ i, (MvPolynomial.X i : MvPolynomial ι ℝ)).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_finset_sum _ _).trans
    apply Finset.sup_le
    intro i _
    simp
  have hsquare : (∑ i, (MvPolynomial.X i : MvPolynomial ι ℝ) ^ 2).totalDegree ≤ 2 := by
    apply (MvPolynomial.totalDegree_finset_sum _ _).trans
    apply Finset.sup_le
    intro i _
    simp
  unfold quadraticExponent
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_smul_le _ _).trans hsquare
  · exact (MvPolynomial.totalDegree_smul_le _ _).trans
      ((MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hlinear))

theorem quadraticExponent_eval (population : ℝ) (value : ι → ℝ) :
    MvPolynomial.eval value (quadraticExponent population) =
      (∑ i, value i ^ 2) / (2 * (population - 1)) -
        (∑ i, value i) ^ 2 / (2 * (population - Fintype.card ι)) := by
  simp [quadraticExponent, MvPolynomial.smul_eq_C_mul, div_eq_mul_inv, mul_comm]

theorem sum_square_bound (value : ι → ℝ) :
    (∑ i, value i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, value i ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ)) value

/-- A uniform bound on the exact quadratic exponent with no dependence on
the maximum clipped coordinate. -/
theorem quadraticExponent_abs (population : ℝ) (value : ι → ℝ)
    (hpopulation : 2 ≤ population) (horder : 2 * (Fintype.card ι : ℝ) ≤ population) :
    |MvPolynomial.eval value (quadraticExponent population)| ≤
      ((Fintype.card ι : ℝ) + 1) / population * ∑ i, value i ^ 2 := by
  have hp : 0 < population := by linarith
  have hd1 : population ≤ 2 * (population - 1) := by linarith
  have hd2 : population ≤ 2 * (population - (Fintype.card ι : ℝ)) := by linarith
  have hs : 0 ≤ ∑ i, value i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : (∑ i, value i ^ 2) / (2 * (population - 1)) ≤
      (∑ i, value i ^ 2) / population := div_le_div_of_nonneg_left hs hp hd1
  have h2 : (∑ i, value i) ^ 2 / (2 * (population - (Fintype.card ι : ℝ))) ≤
      ((Fintype.card ι : ℝ) * ∑ i, value i ^ 2) / population :=
    (div_le_div_of_nonneg_left (sq_nonneg _) hp hd2).trans
      (div_le_div_of_nonneg_right (sum_square_bound value) hp.le)
  rw [quadraticExponent_eval]
  calc
    _ ≤ |(∑ i, value i ^ 2) / (2 * (population - 1))| +
        |(∑ i, value i) ^ 2 / (2 * (population - (Fintype.card ι : ℝ)))| := abs_sub _ _
    _ = (∑ i, value i ^ 2) / (2 * (population - 1)) +
        (∑ i, value i) ^ 2 / (2 * (population - (Fintype.card ι : ℝ))) := by
      rw [abs_of_nonneg (div_nonneg hs (by linarith)),
        abs_of_nonneg (div_nonneg (sq_nonneg _) (by linarith))]
    _ ≤ (∑ i, value i ^ 2) / population +
        ((Fintype.card ι : ℝ) * ∑ i, value i ^ 2) / population := add_le_add h1 h2
    _ = _ := by ring

variable {α : Type*} [Fintype α]

/-- Squared form of the half-order decay, on the genuine finite product
reference, with a completely specified order-dependent constant. -/
theorem quadraticExponent_anova_bound (population parameter bound : ℝ)
    (p : ι → FiniteDist α) (hp : ∀ i a, 0 < (p i).weight a)
    (value : ι → α → ℝ) (hpopulation : 2 ≤ population)
    (horder : 2 * (Fintype.card ι : ℝ) ≤ population)
    (hparameter : 0 < parameter)
    (hsmall : 4 * (((Fintype.card ι : ℝ) + 1) / population) ≤ parameter)
    (hmoment : ∀ i, (p i).expectation (fun a => Real.exp (parameter * value i a ^ 2)) ≤ bound) :
    let order := (Fintype.card ι + 1) / 2
    (FiniteDist.independent p).l2Sq (Hoeffding.projection p Finset.univ (fun x =>
      Real.exp (MvPolynomial.eval (fun i => value i (x i)) (quadraticExponent population)))) ≤
      (((Fintype.card ι : ℝ) + 1) / population) ^ (2 * order) *
        (((2 * order).factorial : ℝ) / (parameter / 2) ^ (2 * order)) *
        bound ^ Fintype.card ι := by
  apply Hoeffding.projection_quadratic_exp_moment_bound p hp Finset.univ value
    (quadraticExponent population) (quadraticExponent_degree population)
  · intro j hj
    simpa only [Finset.card_univ] using Hoeffding.ceiling_half_taylor_order (Fintype.card ι) j hj
  · positivity
  · exact hparameter
  · exact hsmall
  · intro x
    exact quadraticExponent_abs population _ hpopulation horder
  · exact hmoment

end

end AFT.RootSlice

import AFT.QuadraticRootBounds

/-!
# Stability of actual canonical projections under Gaussian approximation

The approximation error is integrated against the actual product reference.
The estimate is independent of alphabet cardinality and retains the quadratic
Taylor gain in the main term.
-/

namespace AFT

open scoped BigOperators Classical

noncomputable section

namespace FiniteDist

variable {α : Type*} [Fintype α]

theorem l2Sq_add_le (p : FiniteDist α) (f g : α → ℝ) :
    p.l2Sq (f + g) ≤ 2 * p.l2Sq f + 2 * p.l2Sq g := by
  unfold l2Sq expectation
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have h : (f x + g x) ^ 2 ≤ 2 * f x ^ 2 + 2 * g x ^ 2 := by
    nlinarith [sq_nonneg (f x - g x)]
  simpa only [Pi.add_apply, mul_add, mul_left_comm] using
    mul_le_mul_of_nonneg_left h (p.nonneg x)

theorem l2Sq_smul (p : FiniteDist α) (c : ℝ) (f : α → ℝ) :
    p.l2Sq (c • f) = c ^ 2 * p.l2Sq f := by
  unfold l2Sq expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end FiniteDist

namespace Hoeffding

variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem projection_perturbation_bound (p : ι → FiniteDist α)
    (hp : ∀ i a, 0 < (p i).weight a) (S : Finset ι)
    (f g : (ι → α) → ℝ) (c : ℝ) :
    (FiniteDist.independent p).l2Sq (projection p S f) ≤
      2 * c ^ 2 * (FiniteDist.independent p).l2Sq (projection p S g) +
        2 * (FiniteDist.independent p).l2Sq (f - c • g) := by
  have heq : projection p S f =
      c • projection p S g + projection p S (f - c • g) := by
    rw [map_sub, map_smul]
    abel
  calc
    _ = (FiniteDist.independent p).l2Sq
        (c • projection p S g + projection p S (f - c • g)) := congrArg _ heq
    _ ≤ 2 * (FiniteDist.independent p).l2Sq (c • projection p S g) +
        2 * (FiniteDist.independent p).l2Sq (projection p S (f - c • g)) :=
      FiniteDist.l2Sq_add_le _ _ _
    _ ≤ _ := by
      rw [FiniteDist.l2Sq_smul]
      have hh := projection_contracts p hp S (f - c • g)
      nlinarith

theorem exponential_error_l2Sq (p : ι → FiniteDist α)
    (f : (ι → α) → ℝ) (exponent : (ι → α) → ℝ)
    (value : ι → α → ℝ) (error rate parameter bound : ℝ)
    (hsmall : 2 * rate ≤ parameter)
    (hexponent : ∀ x, |exponent x| ≤ rate * ∑ i, value i (x i) ^ 2)
    (hf : ∀ x, |f x| ≤ error * Real.exp |exponent x|)
    (hmoment : ∀ i, (p i).expectation
      (fun a => Real.exp (parameter * value i a ^ 2)) ≤ bound) :
    (FiniteDist.independent p).l2Sq f ≤ error ^ 2 * bound ^ Fintype.card ι := by
  have hpoint (x : ι → α) : f x ^ 2 ≤
      error ^ 2 * Real.exp (∑ i, parameter * value i (x i) ^ 2) := by
    have hs : 0 ≤ ∑ i, value i (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc
      _ = |f x| ^ 2 := (sq_abs _).symm
      _ ≤ (error * Real.exp |exponent x|) ^ 2 := by gcongr; exact hf x
      _ = error ^ 2 * Real.exp (2 * |exponent x|) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg error)
        apply Real.exp_le_exp.mpr
        rw [← Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left (hexponent x) (by norm_num : (0 : ℝ) ≤ 2)).trans
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsmall hs)
  calc
    _ ≤ (FiniteDist.independent p).expectation
        (fun x => error ^ 2 * Real.exp (∑ i, parameter * value i (x i) ^ 2)) :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hpoint x) ((FiniteDist.independent p).nonneg x)
    _ = error ^ 2 * (FiniteDist.independent p).expectation
        (fun x => Real.exp (∑ i, parameter * value i (x i) ^ 2)) := by
      unfold FiniteDist.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (FiniteDist.expectation_exp_sum_le p (fun i a => parameter * value i a ^ 2) bound hmoment)
      (sq_nonneg error)

end Hoeffding

namespace RootSlice

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- A relative Gaussian approximation becomes an absolute exponential
envelope without dividing by a quantity of unknown sign. -/
theorem relative_exp_error (actual prefactor exponent error : ℝ)
    (hp : 0 < prefactor)
    (herror : |actual / (prefactor * Real.exp exponent) - 1| ≤ error) :
    |actual - prefactor * Real.exp exponent| ≤
      (prefactor * error) * Real.exp |exponent| := by
  have hm : 0 < prefactor * Real.exp exponent := mul_pos hp (Real.exp_pos _)
  have he : actual - prefactor * Real.exp exponent =
      (actual / (prefactor * Real.exp exponent) - 1) * (prefactor * Real.exp exponent) := by
    field_simp
  have he0 : 0 ≤ error := (abs_nonneg _).trans herror
  rw [he, abs_mul, abs_of_pos hm]
  calc
    _ ≤ error * (prefactor * Real.exp exponent) :=
      mul_le_mul_of_nonneg_right herror hm.le
    _ ≤ (prefactor * error) * Real.exp |exponent| := by
      have hh := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (le_abs_self exponent)) (mul_nonneg hp.le he0)
      simpa only [mul_left_comm error prefactor, mul_assoc] using hh

/-- Perturbed half-order ANOVA decay. All norms and projections are taken
under the actual finite product reference. The negligible error is retained
explicitly rather than silently being dropped by the Taylor argument. -/
theorem quadratic_approximation_anova_bound (population parameter bound prefactor error : ℝ)
    (p : ι → FiniteDist α) (hp : ∀ i a, 0 < (p i).weight a)
    (value : ι → α → ℝ) (density : (ι → α) → ℝ)
    (hpopulation : 2 ≤ population) (horder : 2 * (Fintype.card ι : ℝ) ≤ population)
    (hparameter : 0 < parameter) (hc : 0 < prefactor)
    (hsmall : 4 * (((Fintype.card ι : ℝ) + 1) / population) ≤ parameter)
    (hmoment : ∀ i, (p i).expectation (fun a => Real.exp (parameter * value i a ^ 2)) ≤ bound)
    (happrox : ∀ x, |density x / (prefactor * Real.exp
      (MvPolynomial.eval (fun i => value i (x i)) (quadraticExponent population))) - 1| ≤ error) :
    let order := (Fintype.card ι + 1) / 2
    (FiniteDist.independent p).l2Sq (Hoeffding.projection p Finset.univ density) ≤
      2 * prefactor ^ 2 *
        ((((Fintype.card ι : ℝ) + 1) / population) ^ (2 * order) *
          (((2 * order).factorial : ℝ) / (parameter / 2) ^ (2 * order)) *
          bound ^ Fintype.card ι) +
        2 * (prefactor * error) ^ 2 * bound ^ Fintype.card ι := by
  dsimp only
  let exponent : (ι → α) → ℝ := fun x =>
    MvPolynomial.eval (fun i => value i (x i)) (quadraticExponent population)
  let model : (ι → α) → ℝ := fun x => Real.exp (exponent x)
  have hmain := quadraticExponent_anova_bound population parameter bound p hp value
    hpopulation horder hparameter hsmall hmoment
  have hrate : 0 ≤ ((Fintype.card ι : ℝ) + 1) / population := by positivity
  have herr := Hoeffding.exponential_error_l2Sq p (density - prefactor • model)
    exponent value (prefactor * error) (((Fintype.card ι : ℝ) + 1) / population)
    parameter bound (by linarith)
    (fun x => quadraticExponent_abs population _ hpopulation horder)
    (fun x => relative_exp_error _ _ _ _ hc (happrox x)) hmoment
  have hproj := Hoeffding.projection_perturbation_bound p hp Finset.univ density model prefactor
  calc
    _ ≤ 2 * prefactor ^ 2 * (FiniteDist.independent p).l2Sq
        (Hoeffding.projection p Finset.univ model) +
        2 * (FiniteDist.independent p).l2Sq (density - prefactor • model) := hproj
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ 2 * prefactor ^ 2)
      nlinarith

end RootSlice

end

end AFT

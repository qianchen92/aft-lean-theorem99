import AFT.BlockFock
import AFT.Hoeffding

/-! # Dimension-free concentration on actual finite product laws -/

namespace AFT.FiniteConcentration

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

theorem bounded_centered_mgf (law : FiniteDist Color) (value : Color → ℝ)
    (bound parameter : ℝ) (hbound : 0 ≤ bound)
    (hcenter : law.expectation value = 0) (hvalue : ∀ color, |value color| ≤ bound) :
    law.expectation (fun color => Real.exp (parameter * value color)) ≤
      Real.exp (parameter ^ 2 * bound ^ 2 / 2) := by
  by_cases hz : bound = 0
  · subst bound
    have hv : ∀ color, value color = 0 := fun color => abs_nonpos_iff.mp (hvalue color)
    simp [FiniteDist.expectation, hv, law.sum_one]
  have hb : 0 < bound := lt_of_le_of_ne hbound (Ne.symm hz)
  have hpoint (color : Color) : Real.exp (parameter * value color) ≤
      (bound + value color) / (2 * bound) * Real.exp (parameter * bound) +
        (bound - value color) / (2 * bound) * Real.exp (-parameter * bound) := by
    have hc := convexOn_exp.2 (Set.mem_univ (parameter * bound)) (Set.mem_univ (-parameter * bound))
      (show 0 ≤ (bound + value color) / (2 * bound) from div_nonneg (by linarith [(abs_le.mp (hvalue color)).1]) (by positivity))
      (show 0 ≤ (bound - value color) / (2 * bound) from div_nonneg (by linarith [(abs_le.mp (hvalue color)).2]) (by positivity))
      (show (bound + value color) / (2 * bound) + (bound - value color) / (2 * bound) = 1 by field_simp; ring)
    convert hc using 1
    congr 1
    simp only [smul_eq_mul]
    field_simp
    ring
  have hh := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint color) (law.nonneg color))
  have heq : (∑ color, law.weight color *
      ((bound + value color) / (2 * bound) * Real.exp (parameter * bound) +
        (bound - value color) / (2 * bound) * Real.exp (-parameter * bound))) = Real.cosh (parameter * bound) := by
    calc
      _ = ((bound * ∑ color, law.weight color) + (∑ color, law.weight color * value color)) /
          (2 * bound) * Real.exp (parameter * bound) +
        ((bound * ∑ color, law.weight color) - (∑ color, law.weight color * value color)) /
          (2 * bound) * Real.exp (-parameter * bound) := by
          simp only [add_div, sub_div, add_mul, sub_mul, mul_add, mul_sub,
            Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
          simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro color _
          ring
      _ = _ := by
        change ((bound * _) + law.expectation value) / _ * _ +
          ((bound * _) - law.expectation value) / _ * _ = _
        rw [law.sum_one, hcenter, Real.cosh_eq]
        field_simp
        ring
  apply (hh.trans_eq heq).trans
  simpa only [mul_pow] using Real.cosh_le_exp_half_sq (parameter * bound)

theorem expectation_cons (count : ℕ) (law : Fin (count + 1) → FiniteDist Color)
    (value : (Fin (count + 1) → Color) → ℝ) :
    (FiniteDist.independent law).expectation value =
      (law 0).expectation (fun first =>
        (FiniteDist.independent (fun index => law index.succ)).expectation
          (fun rest => value (Fin.cons first rest))) := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (count + 1) => Color))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  change (∏ index, (law index).weight ((Fin.cons first rest : Fin (count + 1) → Color) index)) * value (Fin.cons first rest) = _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem expectation_abs_sub_le (law : FiniteDist Color) (value : Color → ℝ) (bound : ℝ)
    (h : ∀ first second, |value first - value second| ≤ bound) (first : Color) :
    |value first - law.expectation value| ≤ bound := by
  have heq : value first - law.expectation value = ∑ second, law.weight second * (value first - value second) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, law.sum_one, one_mul,
      FiniteDist.expectation]
  rw [heq]
  calc
    _ ≤ ∑ second, |law.weight second * (value first - value second)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ second, law.weight second * bound := by
      apply Finset.sum_le_sum
      intro second _
      rw [abs_mul, abs_of_nonneg (law.nonneg second)]
      exact mul_le_mul_of_nonneg_left (h first second) (law.nonneg second)
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]

/-- Coordinate oscillations, with all other sample values fixed. -/
def BoundedDifferences (count : ℕ) (value : (Fin count → Color) → ℝ) (bound : Fin count → ℝ) : Prop :=
  ∀ index first second, (∀ other, other ≠ index → first other = second other) →
    |value first - value second| ≤ bound index

theorem bounded_differences_mgf (count : ℕ) (law : Fin count → FiniteDist Color)
    (value : (Fin count → Color) → ℝ) (bound : Fin count → ℝ)
    (hbound : ∀ index, 0 ≤ bound index) (hdiff : BoundedDifferences count value bound)
    (parameter : ℝ) :
    (FiniteDist.independent law).expectation
      (fun word => Real.exp (parameter * (value word - (FiniteDist.independent law).expectation value))) ≤
        Real.exp (parameter ^ 2 * (∑ index, bound index ^ 2) / 2) := by
  induction count with
  | zero =>
    have hc (word : Fin 0 → Color) : (FiniteDist.independent law).expectation value = value word := by
      unfold FiniteDist.expectation
      have hv (other : Fin 0 → Color) : value other = value word := congrArg value (Subsingleton.elim _ _)
      simp only [hv, ← Finset.sum_mul, (FiniteDist.independent law).sum_one, one_mul]
    have hz : (fun word => Real.exp (parameter * (value word - (FiniteDist.independent law).expectation value))) =
        (fun _ => (1 : ℝ)) := by funext word; rw [hc word]; simp
    rw [hz]
    simp only [FiniteDist.expectation, mul_one, (FiniteDist.independent law).sum_one,
      Fin.sum_univ_zero, mul_zero, zero_div, Real.exp_zero, le_refl]
  | succ count ih =>
    let tailLaw := FiniteDist.independent (fun index : Fin count => law index.succ)
    let average (first : Color) := tailLaw.expectation (fun rest => value (Fin.cons first rest))
    have htail (first : Color) : BoundedDifferences count (fun rest => value (Fin.cons first rest)) (fun index => bound index.succ) := by
      intro index rest other hsame
      apply hdiff index.succ (Fin.cons first rest) (Fin.cons first other)
      intro position hposition
      cases position using Fin.cases with
      | zero => rfl
      | succ position =>
        exact hsame position (by simpa only [ne_eq, Fin.succ_inj] using hposition)
    have havg (first second : Color) : |average first - average second| ≤ bound 0 := by
      have heq : average first - average second =
          ∑ rest, tailLaw.weight rest * (value (Fin.cons first rest) - value (Fin.cons second rest)) := by
        simp only [average, FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib]
      rw [heq]
      calc
        _ ≤ ∑ rest, |tailLaw.weight rest * (value (Fin.cons first rest) - value (Fin.cons second rest))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ rest, tailLaw.weight rest * bound 0 := by
          apply Finset.sum_le_sum
          intro rest _
          rw [abs_mul, abs_of_nonneg (tailLaw.nonneg rest)]
          apply mul_le_mul_of_nonneg_left _ (tailLaw.nonneg rest)
          apply hdiff 0
          intro position hposition
          cases position using Fin.cases with
          | zero => contradiction
          | succ position => rfl
        _ = _ := by rw [← Finset.sum_mul, tailLaw.sum_one, one_mul]
    have hcenter : (law 0).expectation (fun first => average first - (law 0).expectation average) = 0 := by
      simp only [FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (law 0).sum_one, one_mul, sub_self]
    have hfirst := bounded_centered_mgf (law 0) (fun first => average first - (law 0).expectation average)
      (bound 0) parameter (hbound 0) hcenter (expectation_abs_sub_le (law 0) average (bound 0) havg)
    have htailmgf (first : Color) := ih (fun index => law index.succ) (fun rest => value (Fin.cons first rest))
      (fun index => bound index.succ) (fun index => hbound index.succ) (htail first)
    rw [expectation_cons]
    have hmean : (FiniteDist.independent law).expectation value = (law 0).expectation average := expectation_cons count law value
    simp only [hmean]
    calc
      _ = (law 0).expectation (fun first =>
        Real.exp (parameter * (average first - (law 0).expectation average)) *
          tailLaw.expectation (fun rest => Real.exp (parameter * (value (Fin.cons first rest) - average first)))) := by
          unfold FiniteDist.expectation
          apply Finset.sum_congr rfl
          intro first _
          dsimp only
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro rest _
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
      _ ≤ (law 0).expectation (fun first =>
        Real.exp (parameter * (average first - (law 0).expectation average)) *
          Real.exp (parameter ^ 2 * (∑ index : Fin count, bound index.succ ^ 2) / 2)) := by
          apply Finset.sum_le_sum
          intro first _
          apply mul_le_mul_of_nonneg_left _ ((law 0).nonneg first)
          exact mul_le_mul_of_nonneg_left (htailmgf first) (Real.exp_nonneg _)
      _ = (law 0).expectation (fun first => Real.exp (parameter * (average first - (law 0).expectation average))) *
          Real.exp (parameter ^ 2 * (∑ index : Fin count, bound index.succ ^ 2) / 2) := by
          simp only [FiniteDist.expectation, ← mul_assoc, ← Finset.sum_mul]
      _ ≤ Real.exp (parameter ^ 2 * bound 0 ^ 2 / 2) *
          Real.exp (parameter ^ 2 * (∑ index : Fin count, bound index.succ ^ 2) / 2) :=
          mul_le_mul_of_nonneg_right hfirst (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, Fin.sum_univ_succ]; congr 1; ring

end

end AFT.FiniteConcentration

import AFT.SquareConcentration

/-! # Exponential-square concentration for genuine independent Hilbert sums -/

namespace AFT.FiniteConcentration

open scoped BigOperators Classical

noncomputable section

variable {Color Hilbert : Type*} [Fintype Color]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

def vectorMean (law : FiniteDist Color) (value : Color → Hilbert) : Hilbert :=
  ∑ color, law.weight color • value color

theorem centered_add_energy (law : FiniteDist Color) (value : Color → Hilbert)
    (hcenter : vectorMean law value = 0) (fixed : Hilbert) :
    law.expectation (fun color => ‖value color + fixed‖ ^ 2) =
      law.expectation (fun color => ‖value color‖ ^ 2) + ‖fixed‖ ^ 2 := by
  have hcross : (∑ color, law.weight color * inner ℝ (value color) fixed) = 0 := by
    rw [← show inner ℝ (vectorMean law value) fixed =
      ∑ color, law.weight color * inner ℝ (value color) fixed by
        simp only [vectorMean, sum_inner, real_inner_smul_left]]
    rw [hcenter, inner_zero_left]
  simp only [FiniteDist.expectation, norm_add_sq_real, mul_add, Finset.sum_add_distrib]
  have heq : (∑ color, law.weight color * (2 * inner ℝ (value color) fixed)) =
      2 * ∑ color, law.weight color * inner ℝ (value color) fixed := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro color _
    ring
  rw [heq, hcross, mul_zero, add_zero, ← Finset.sum_mul, law.sum_one, one_mul]

theorem independent_sum_energy (count : ℕ) (law : Fin count → FiniteDist Color)
    (value : Fin count → Color → Hilbert) (hcenter : ∀ index, vectorMean (law index) (value index) = 0) :
    (FiniteDist.independent law).expectation (fun word => ‖∑ index, value index (word index)‖ ^ 2) =
      ∑ index, (law index).expectation (fun color => ‖value index color‖ ^ 2) := by
  induction count with
  | zero => simp [FiniteDist.expectation]
  | succ count ih =>
    rw [expectation_cons]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    unfold FiniteDist.expectation
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hstep (rest : Fin count → Color) :
        (∑ color, (law 0).weight color * ‖value 0 color + ∑ index : Fin count, value index.succ (rest index)‖ ^ 2) =
          (law 0).expectation (fun color => ‖value 0 color‖ ^ 2) + ‖∑ index : Fin count, value index.succ (rest index)‖ ^ 2 :=
      centered_add_energy (law 0) (value 0) (hcenter 0) _
    calc
      _ = ∑ rest, (FiniteDist.independent (fun index : Fin count => law index.succ)).weight rest *
          ((law 0).expectation (fun color => ‖value 0 color‖ ^ 2) + ‖∑ index : Fin count, value index.succ (rest index)‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro rest _
        rw [← hstep, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        ring
      _ = _ := by
        rw [show (∑ rest, (FiniteDist.independent (fun index : Fin count => law index.succ)).weight rest *
          ((law 0).expectation (fun color => ‖value 0 color‖ ^ 2) + ‖∑ index : Fin count, value index.succ (rest index)‖ ^ 2)) =
          (law 0).expectation (fun color => ‖value 0 color‖ ^ 2) +
          (FiniteDist.independent (fun index : Fin count => law index.succ)).expectation (fun rest => ‖∑ index : Fin count, value index.succ (rest index)‖ ^ 2) by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
              (FiniteDist.independent (fun index : Fin count => law index.succ)).sum_one, one_mul, FiniteDist.expectation]]
        rw [ih (fun index : Fin count => law index.succ) (fun index => value index.succ) (fun index => hcenter index.succ)]
        rfl

omit [Fintype Color] [InnerProductSpace ℝ Hilbert] in
theorem norm_sum_boundedDifferences (count : ℕ) (value : Fin count → Color → Hilbert)
    (bound : Fin count → ℝ) (hbound : ∀ index color, ‖value index color‖ ≤ bound index) :
    BoundedDifferences count (fun word => ‖∑ index, value index (word index)‖) (fun index => 2 * bound index) := by
  intro index first second hsame
  have hdiff : (∑ other, value other (first other)) - (∑ other, value other (second other)) =
      value index (first index) - value index (second index) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single index
    · intro other _ hother
      rw [hsame other hother, sub_self]
    · simp
  calc
    _ ≤ ‖(∑ other, value other (first other)) - (∑ other, value other (second other))‖ := abs_norm_sub_norm_le _ _
    _ = _ := congrArg norm hdiff
    _ ≤ ‖value index (first index)‖ + ‖value index (second index)‖ := norm_sub_le _ _
    _ ≤ _ := by linarith [hbound index (first index), hbound index (second index)]

omit [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert] in
theorem scalar_mean_sq_le (law : FiniteDist Color) (value : Color → ℝ) :
    law.expectation value ^ 2 ≤ law.l2Sq value := by
  have hh : (∑ color, law.weight color * value color) ^ 2 ≤
      (∑ color, law.weight color) * (∑ color, law.weight color * value color ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro color _; exact law.nonneg color
    · intro color _; exact mul_nonneg (law.nonneg color) (sq_nonneg _)
    · intro color _; ring
  simpa only [law.sum_one, one_mul] using hh

/-- A full exponential-square estimate with variance budget equal to the
sum of squared coordinate bounds; there is no Hilbert-dimension factor. -/
theorem hilbert_sum_square_mgf (count : ℕ) (law : Fin count → FiniteDist Color)
    (value : Fin count → Color → Hilbert) (bound : Fin count → ℝ)
    (hcenter : ∀ index, vectorMean (law index) (value index) = 0)
    (hbound : ∀ index, 0 ≤ bound index) (hvalue : ∀ index color, ‖value index color‖ ≤ bound index)
    (parameter : ℝ) (hparameter : 0 ≤ parameter)
    (hsmall : 16 * parameter * (∑ index, bound index ^ 2) < 1) :
    (FiniteDist.independent law).expectation
      (fun word => Real.exp (parameter * ‖∑ index, value index (word index)‖ ^ 2)) ≤
        Real.exp (2 * parameter * ∑ index, bound index ^ 2) *
          (Real.sqrt (1 - 16 * parameter * ∑ index, bound index ^ 2))⁻¹ := by
  let product := FiniteDist.independent law
  let size (word : Fin count → Color) := ‖∑ index, value index (word index)‖
  let mean := product.expectation size
  let budget := ∑ index, bound index ^ 2
  have henergy : product.l2Sq size ≤ budget := by
    rw [FiniteDist.l2Sq, independent_sum_energy count law value hcenter]
    apply Finset.sum_le_sum
    intro index _
    calc
      _ ≤ ∑ color, (law index).weight color * bound index ^ 2 := by
        apply Finset.sum_le_sum
        intro color _
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hvalue index color) 2) ((law index).nonneg color)
      _ = _ := by rw [← Finset.sum_mul, (law index).sum_one, one_mul]
  have hmean : mean ^ 2 ≤ budget := (scalar_mean_sq_le product size).trans henergy
  have hmgf (test : ℝ) : product.expectation (fun word => Real.exp (test * (size word - mean))) ≤
      Real.exp ((4 * budget) * test ^ 2 / 2) := by
    have hh := bounded_differences_mgf count law size (fun index => 2 * bound index)
      (fun index => mul_nonneg (by norm_num) (hbound index)) (norm_sum_boundedDifferences count value bound hvalue) test
    have heq : (∑ index, (2 * bound index) ^ 2) = 4 * budget := by
      simp only [budget, mul_pow, Finset.mul_sum]
      norm_num
    simpa only [heq, mul_comm (test ^ 2)] using hh
  have hquad := subGaussian_square_mgf product (fun word => size word - mean) (4 * budget) (2 * parameter)
    (by positivity) (by dsimp [budget]; nlinarith [hsmall]) hmgf
  have hpoint (word : Fin count → Color) : Real.exp (parameter * size word ^ 2) ≤
      Real.exp (2 * parameter * budget) * Real.exp ((2 * parameter) * (size word - mean) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs : size word ^ 2 ≤ 2 * (size word - mean) ^ 2 + 2 * budget := by
      nlinarith [sq_nonneg (size word - 2 * mean)]
    nlinarith
  have hh := Finset.sum_le_sum (fun word (_ : word ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint word) (product.nonneg word))
  have heq : (∑ word, product.weight word *
      (Real.exp (2 * parameter * budget) * Real.exp ((2 * parameter) * (size word - mean) ^ 2))) =
      Real.exp (2 * parameter * budget) * product.expectation
        (fun word => Real.exp ((2 * parameter) * (size word - mean) ^ 2)) := by
    simp only [FiniteDist.expectation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word _
    ring
  rw [heq] at hh
  have hfinal := hh.trans (mul_le_mul_of_nonneg_left hquad (Real.exp_nonneg _))
  convert hfinal using 1
  congr 3
  ring

end

end AFT.FiniteConcentration

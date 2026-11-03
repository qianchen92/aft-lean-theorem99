import AFT.MixedProducts

/-! # Canonicalization of actual density kernels under a comparable reference -/

namespace AFT.MixedKernel

open scoped BigOperators Classical
noncomputable section

variable {Color : Type*} [Fintype Color]

def rowAverage (p : FiniteDist Color) (kernel : Color → Color → ℝ) (x : Color) : ℝ :=
  ∑ y, p.weight y * kernel x y

def columnAverage (p : FiniteDist Color) (kernel : Color → Color → ℝ) (y : Color) : ℝ :=
  ∑ x, p.weight x * kernel x y

def centeredPairDensity (p : FiniteDist Color) (referenceRatio : Color → ℝ)
    (kernel : Color → Color → ℝ) (x y : Color) : ℝ :=
  kernel x y - referenceRatio x * columnAverage p kernel y - rowAverage p kernel x * referenceRatio y

theorem rowAverage_square_le (p : FiniteDist Color) (kernel : Color → Color → ℝ) (x : Color) :
    rowAverage p kernel x ^ 2 ≤ ∑ y, p.weight y * kernel x y ^ 2 := by
  have hh : (∑ y, p.weight y * kernel x y)^2 ≤
      (∑ y, p.weight y) * ∑ y, p.weight y * kernel x y^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro y _; exact p.nonneg y
    · intro y _; exact mul_nonneg (p.nonneg y) (sq_nonneg _)
    · intro y _; ring
  simpa only [p.sum_one, one_mul] using hh

theorem rowAverage_bounds (p : FiniteDist Color) (kernel : Color → Color → ℝ) (F X : ℝ)
    (hfull : (∑ x, ∑ y, p.weight x*p.weight y*kernel x y^2) ≤ F^2)
    (hpoint : ∀ x y, |kernel x y| ≤ X) :
    (∑ x, p.weight x * rowAverage p kernel x^2) ≤ F^2 ∧
      ∀ x, |rowAverage p kernel x| ≤ X := by
  constructor
  · calc
      _ ≤ ∑ x, p.weight x * ∑ y, p.weight y * kernel x y^2 :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (rowAverage_square_le p kernel x) (p.nonneg x)
      _ = ∑ x, ∑ y, p.weight x*p.weight y*kernel x y^2 := by simp only [Finset.mul_sum, mul_assoc]
      _ ≤ _ := hfull
  · intro x
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ y, p.weight y*X := by
        apply Finset.sum_le_sum
        intro y _
        rw [abs_mul, abs_of_nonneg (p.nonneg y)]
        exact mul_le_mul_of_nonneg_left (hpoint x y) (p.nonneg y)
      _ = _ := by rw [← Finset.sum_mul, p.sum_one, one_mul]

theorem columnAverage_bounds (p : FiniteDist Color) (kernel : Color → Color → ℝ) (F X : ℝ)
    (hfull : (∑ x, ∑ y, p.weight x*p.weight y*kernel x y^2) ≤ F^2)
    (hpoint : ∀ x y, |kernel x y| ≤ X) :
    (∑ y, p.weight y * columnAverage p kernel y^2) ≤ F^2 ∧
      ∀ y, |columnAverage p kernel y| ≤ X := by
  apply rowAverage_bounds p (fun y x => kernel x y) F X _ (fun y x => hpoint x y)
  rw [Finset.sum_comm]
  convert hfull using 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- This includes the integrated fiber and every fixed-coordinate fiber;
the two reference corrections are explicit products of true marginals. -/
theorem centeredPair_activity_le (p : FiniteDist Color) (R : Color → ℝ) (kernel : Color → Color → ℝ)
    (a F X : ℝ) (ha : 0 ≤ a) (hF : 0 ≤ F) (hX : 0 ≤ X)
    (hR : ∀ x, |R x| ≤ 8) (hR2 : (∑ x, p.weight x*R x^2) ≤ 3^2)
    (hfull : (∑ x, ∑ y, p.weight x*p.weight y*kernel x y^2) ≤ F^2)
    (hpoint : ∀ x y, |kernel x y| ≤ X) :
    activity ![a,a] (pairReference p p) (pairKernel (centeredPairDensity p R kernel)) ≤
      a*a*(F+a*X+a*X+a*a*X) + 2*a*a*(3+8*a)*(F+a*X) := by
  have hrow := rowAverage_bounds p kernel F X hfull hpoint
  have hcol := columnAverage_bounds p kernel F X hfull hpoint
  have hfirst (x) : (∑ y, p.weight y*kernel x y^2) ≤ X^2 := by
    calc
      _ ≤ ∑ y, p.weight y*X^2 := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hpoint x y) 2) (p.nonneg y)
      _ = _ := by rw [← Finset.sum_mul, p.sum_one, one_mul]
  have hsecond (y) : (∑ x, p.weight x*kernel x y^2) ≤ X^2 := by
    calc
      _ ≤ ∑ x, p.weight x*X^2 := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hpoint x y) 2) (p.nonneg x)
      _ = _ := by rw [← Finset.sum_mul, p.sum_one, one_mul]
  have hK := pair_activity_le p p kernel a a F X X X ha ha hF hX hX hX hfull hfirst hsecond hpoint
  have hRM := pair_product_activity_le p p R (columnAverage p kernel) a a 3 8 F X
    ha ha (by norm_num) (by norm_num) hF hX hR2 hR hcol.1 hcol.2
  have hMR := pair_product_activity_le p p (rowAverage p kernel) R a a F X 3 8
    ha ha hF hX (by norm_num) (by norm_num) hrow.1 hrow.2 hR2 hR
  have hrate : ∀ i : Fin 2, 0 ≤ ![a,a] i := by intro i; fin_cases i <;> exact ha
  have hsub1 := activity_sub_le ![a,a] (pairReference p p) (pairKernel kernel)
    (pairKernel (fun x y => R x * columnAverage p kernel y)) hrate
  have hsub2 := activity_sub_le ![a,a] (pairReference p p)
    (pairKernel kernel - pairKernel (fun x y => R x * columnAverage p kernel y))
    (pairKernel (fun x y => rowAverage p kernel x * R y)) hrate
  change activity ![a,a] (pairReference p p)
    (pairKernel kernel - pairKernel (fun x y => R x * columnAverage p kernel y) -
      pairKernel (fun x y => rowAverage p kernel x * R y)) ≤ _
  linear_combination hsub2 + hsub1 + hK + hRM + hMR

end
end AFT.MixedKernel

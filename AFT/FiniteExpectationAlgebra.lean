import AFT.BodyBlur
import AFT.FiniteRetype

/-! # Exact finite scalar expectation identities -/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

omit [Fintype β] [Fintype ι] in
theorem expectation_const (law : FiniteDist α) (value : ℝ) :
    law.expectation (fun _ => value) = value := by
  simp only [expectation, ← Finset.sum_mul, law.sum_one, one_mul]

omit [Fintype β] [Fintype ι] in
theorem expectation_add (law : FiniteDist α) (f g : α → ℝ) :
    law.expectation (fun x => f x + g x) = law.expectation f + law.expectation g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

omit [Fintype β] [Fintype ι] in
theorem expectation_sub (law : FiniteDist α) (f g : α → ℝ) :
    law.expectation (fun x => f x - g x) = law.expectation f - law.expectation g := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

omit [Fintype β] [Fintype ι] in
theorem expectation_const_mul (law : FiniteDist α) (scalar : ℝ) (f : α → ℝ) :
    law.expectation (fun x => scalar * f x) = scalar * law.expectation f := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype β] [Fintype ι] in
theorem expectation_mul_const (law : FiniteDist α) (f : α → ℝ) (scalar : ℝ) :
    law.expectation (fun x => f x * scalar) = law.expectation f * scalar := by
  simp only [expectation, ← mul_assoc, Finset.sum_mul]

omit [Fintype β] in
theorem expectation_sum (law : FiniteDist α) (f : ι → α → ℝ) :
    law.expectation (fun x => ∑ i, f i x) = ∑ i, law.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [Fintype ι] in
theorem expectation_comm (first : FiniteDist α) (second : FiniteDist β) (f : α → β → ℝ) :
    first.expectation (fun x => second.expectation (f x)) =
      second.expectation (fun y => first.expectation (fun x => f x y)) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype ι] in
theorem expectation_prod (first : FiniteDist α) (second : FiniteDist β) (f : α × β → ℝ) :
    (first.prod second).expectation f =
      first.expectation (fun x => second.expectation (fun y => f (x,y))) := by
  simp only [expectation, prod_weight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

omit [Fintype β] [Fintype ι] in
theorem expectation_optional (law : FiniteDist α) (rate : ℝ) (hzero hone) (f : Option α → ℝ) :
    (optional law rate hzero hone).expectation f =
      (1 - rate) * f none + rate * law.expectation (fun x => f (some x)) := by
  simp only [expectation, Fintype.sum_option, optional_none, optional_some, Finset.mul_sum,
    mul_assoc]

theorem expectation_retype {α : Type*} {source : Fintype α} [target : Fintype α]
    (law : @FiniteDist α source) (f : α → ℝ) :
    (retype law).expectation f = @expectation α source law f := by
  cases Subsingleton.elim source target
  rfl

end
end AFT.FiniteDist

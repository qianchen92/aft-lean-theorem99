import AFT.Hoeffding

/-! # Finite moment triangle bound without a number-of-terms loss -/

namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State Index : Type*} [Fintype State] [Fintype Index]

theorem zero_moment_positive_atom (law : FiniteDist State) (value : State → ℝ)
    (power : ℕ) (hpower : 0 < power)
    (hmoment : law.expectation (fun point => |value point|^power) ≤ 0)
    (point : State) (hpoint : 0 < law.weight point) : value point = 0 := by
  have ht : law.weight point * |value point|^power ≤ 0 :=
    (Finset.single_le_sum (f := fun x => law.weight x * |value x|^power) (fun x _ => mul_nonneg (law.nonneg x) (pow_nonneg (abs_nonneg (value x)) power))
      (Finset.mem_univ point)).trans hmoment
  have hp : |value point|^power = 0 := le_antisymm (by nlinarith) (by positivity)
  exact abs_eq_zero.mp ((pow_eq_zero_iff hpower.ne').mp hp)

/-- Finite Minkowski for a probability law. Zero norm bounds are allowed,
and no factor depending on the number of represented terms is introduced. -/
theorem expectation_abs_sum_pow_le (law : FiniteDist State) (value : Index → State → ℝ)
    (bound : Index → ℝ) (hbound : ∀ index, 0 ≤ bound index)
    (power : ℕ) (hpower : 0 < power)
    (hmoment : ∀ index, law.expectation (fun point => |value index point|^power) ≤ bound index^power) :
    law.expectation (fun point => |∑ index, value index point|^power) ≤ (∑ index, bound index)^power := by
  let total := ∑ index, bound index
  have htotal : 0 ≤ total := Finset.sum_nonneg fun index _ => hbound index
  have hz (index : Index) (hi : bound index = 0) (point : State) (hp : 0 < law.weight point) :
      value index point = 0 :=
    zero_moment_positive_atom law (value index) power hpower (by simpa only [hi, zero_pow hpower.ne'] using hmoment index) point hp
  by_cases ht : total = 0
  · have hall (index : Index) : bound index = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun index _ => hbound index)).mp ht index (Finset.mem_univ _)
    change (∑ point, law.weight point * |∑ index, value index point|^power) ≤ total^power
    rw [ht, zero_pow hpower.ne']
    apply Finset.sum_nonpos
    intro point _
    by_cases hp : law.weight point = 0
    · simp only [hp, zero_mul, le_refl]
    · have hpoint := (law.nonneg point).lt_of_ne' hp
      simp only [hz _ (hall _) point hpoint, Finset.sum_const_zero, abs_zero, zero_pow hpower.ne', mul_zero, le_refl]
  have htpos : 0 < total := lt_of_le_of_ne htotal (Ne.symm ht)
  have hw : ∑ index, bound index / total = 1 := by rw [← Finset.sum_div]; exact div_self ht
  have hnormalize (index : Index) :
      law.expectation (fun point => (|value index point| / bound index)^power) ≤ 1 := by
    by_cases hb : bound index = 0
    · simp only [hb, div_zero, zero_pow hpower.ne', expectation, mul_zero, Finset.sum_const_zero, zero_le_one]
    · unfold expectation
      simp only [div_pow, ← mul_div_assoc, ← Finset.sum_div]
      apply (div_le_one (pow_pos (lt_of_le_of_ne (hbound index) (Ne.symm hb)) power)).mpr
      exact hmoment index
  have hpoint (point : State) :
      law.weight point * |∑ index, value index point|^power ≤
        law.weight point * (total^power * ∑ index, (bound index / total) * (|value index point| / bound index)^power) := by
    by_cases hp : law.weight point = 0
    · simp only [hp, zero_mul, le_refl]
    have hpoint := (law.nonneg point).lt_of_ne' hp
    have heq : (∑ index, (bound index / total) * (|value index point| / bound index)) =
        (∑ index, |value index point|) / total := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro index _
      by_cases hb : bound index = 0
      · simp only [hb, hz index hb point hpoint, abs_zero, zero_div, mul_zero]
      · field_simp
    have hj := Real.pow_arith_mean_le_arith_mean_pow Finset.univ
      (fun index => bound index / total) (fun index => |value index point| / bound index)
      (fun index _ => div_nonneg (hbound index) htpos.le) hw
      (fun index _ => div_nonneg (abs_nonneg _) (hbound index)) power
    rw [heq, div_pow] at hj
    apply mul_le_mul_of_nonneg_left _ (law.nonneg point)
    apply (pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) power).trans
    exact (div_le_iff₀ (pow_pos htpos power)).mp hj |>.trans_eq (by ring)
  unfold expectation
  apply (Finset.sum_le_sum fun point _ => hpoint point).trans
  calc
    _ = total^power * ∑ index, (bound index / total) *
        law.expectation (fun point => (|value index point| / bound index)^power) := by
      unfold expectation
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro index _
      apply Finset.sum_congr rfl
      intro point _
      ring
    _ ≤ total^power * ∑ index, (bound index / total) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg htpos.le power)
      exact Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hnormalize index)
        (div_nonneg (hbound index) htpos.le)
    _ = _ := by simp only [mul_one, hw]; rfl


/-- Signed coefficients are charged once in the norm sum. -/
theorem expectation_abs_signed_sum_pow_le (law : FiniteDist State)
    (coefficient : Index → ℝ) (value : Index → State → ℝ) (bound : Index → ℝ)
    (hbound : ∀ index, 0 ≤ bound index) (power : ℕ) (hpower : 0 < power)
    (hmoment : ∀ index, law.expectation (fun point => |value index point|^power) ≤ bound index^power) :
    law.expectation (fun point => |∑ index, coefficient index * value index point|^power) ≤
      (∑ index, |coefficient index| * bound index)^power := by
  apply expectation_abs_sum_pow_le law (fun index point => coefficient index * value index point)
    (fun index => |coefficient index| * bound index)
    (fun index => mul_nonneg (abs_nonneg _) (hbound index)) power hpower
  intro index
  unfold expectation
  simp only [abs_mul, mul_pow]
  calc
    _ = |coefficient index|^power * law.expectation (fun point => |value index point|^power) := by
      unfold expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro point _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmoment index) (pow_nonneg (abs_nonneg _) _)

end
end AFT.FiniteDist

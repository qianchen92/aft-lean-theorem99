import CurrentAFT.RationalFamilyPowerBounds

/-! # Polynomial population losses in truncated binomial evaluation -/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem binomial_error {Primary Body : Type*} (order population : ℕ)
    (table computed : Table ℝ Primary Body order) (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound)
    (herror : ∀ arity colors centers, |computed arity colors centers - table arity colors centers| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |binomial order population computed arity colors centers - binomial order population table arity colors centers| ≤
      ((population+1 : ℕ):ℝ)^(order+1) * ((order+1 : ℕ):ℝ)^2 * error *
        (growth order bound error)^(order+1) := by
  let scale := growth order bound error
  have hs : 1 ≤ scale := growth_ge_one order bound error hb he
  unfold binomial
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1),
        ((population+1 : ℕ):ℝ)^(order+1) * (((order+1 : ℕ):ℝ)*error*scale^(order+1)) := by
      apply Finset.sum_le_sum
      intro count hcount
      have hc : count ≤ order+1 := by have := Finset.mem_range.mp hcount; omega
      have hchoose : (population.choose count : ℝ) ≤ ((population+1 : ℕ):ℝ)^(order+1) := by
        exact_mod_cast (Nat.choose_le_pow population count).trans
          ((Nat.pow_le_pow_left (by omega : population ≤ population+1) count).trans
            (Nat.pow_le_pow_right (by omega : 1 ≤ population+1) hc))
      have hp := power_error order table computed bound error scale hb he hs
        (growth_scale order bound error) htable herror count arity colors centers
      have hp' : |power order computed count arity colors centers-power order table count arity colors centers| ≤
          ((order+1 : ℕ):ℝ)*error*scale^(order+1) := by
        apply hp.trans
        exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) he)
          (pow_le_pow_right₀ hs hc) (by positivity) (by positivity)
      rw [← mul_sub, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ population.choose count by positivity)]
      exact mul_le_mul hchoose hp' (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp only [scale]; ring

end
end CurrentAFT.RationalFamilyProductProgram

import CurrentAFT.RationalFamilyPowerBounds

/-! # Error of the explicit finite reciprocal table -/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

theorem reciprocal_bound {Primary Body : Type*} (order : ℕ) (table : Table ℝ Primary Body order)
    (bound : ℝ) (hb : 0 ≤ bound)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |reciprocal order table arity colors centers| ≤
      ((order+1 : ℕ):ℝ) * (growth order (1+bound) 0)^order := by
  let scale := growth order (1+bound) 0
  have hs : 1 ≤ scale := growth_ge_one order (1+bound) 0 (by positivity) (by norm_num)
  have htable' (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
      (centers : Fin arity.val.2.val → Body) :
      |(unit order - table : Table ℝ Primary Body order) arity colors centers| ≤ 1+bound :=
    (abs_sub _ _).trans (add_le_add (unit_bound order arity colors centers) (htable arity colors centers))
  have hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * (1+bound) ≤ scale := by
    dsimp [scale, growth]
    nlinarith [sq_nonneg (Nat.card (TruncatedArity order) : ℝ)]
  unfold reciprocal
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1), scale^order := by
      apply Finset.sum_le_sum
      intro count hcount
      exact (power_bound order (unit order - table) (1+bound) scale (by positivity) hs hscale
        htable' count arity colors centers).trans (pow_le_pow_right₀ hs (by
          have := Finset.mem_range.mp hcount; omega))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rfl

theorem reciprocal_error {Primary Body : Type*} (order : ℕ) (table computed : Table ℝ Primary Body order)
    (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound)
    (herror : ∀ arity colors centers, |computed arity colors centers - table arity colors centers| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |reciprocal order computed arity colors centers - reciprocal order table arity colors centers| ≤
      ((order+1 : ℕ):ℝ)^2 * error * (growth order (1+bound) error)^(order+1) := by
  let scale := growth order (1+bound) error
  have hs : 1 ≤ scale := growth_ge_one order (1+bound) error (by positivity) he
  have htable' (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
      (centers : Fin arity.val.2.val → Body) : |(unit order - table : Table ℝ Primary Body order) arity colors centers| ≤ 1+bound :=
    (abs_sub _ _).trans (add_le_add (unit_bound order arity colors centers) (htable arity colors centers))
  have herror' (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
      (centers : Fin arity.val.2.val → Body) :
      |(unit order - computed : Table ℝ Primary Body order) arity colors centers - (unit order - table : Table ℝ Primary Body order) arity colors centers| ≤ error := by
    change |(unit order arity colors centers - computed arity colors centers) -
      (unit order arity colors centers - table arity colors centers)| ≤ error
    rw [sub_sub_sub_cancel_left, abs_sub_comm]
    exact herror arity colors centers
  unfold reciprocal
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1), ((order+1 : ℕ):ℝ)*error*scale^(order+1) := by
      apply Finset.sum_le_sum
      intro count hcount
      have hc : count ≤ order+1 := by have := Finset.mem_range.mp hcount; omega
      have h := power_error order (unit order - table : Table ℝ Primary Body order) (unit order - computed : Table ℝ Primary Body order)
        (1+bound) error scale (by positivity) he hs (growth_scale order (1+bound) error)
        htable' herror' count arity colors centers
      apply h.trans
      apply mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) he)
        (pow_le_pow_right₀ hs hc) (by positivity) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp only [scale]; ring

end
end CurrentAFT.RationalFamilyProductProgram

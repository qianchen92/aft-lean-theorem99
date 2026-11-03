import CurrentAFT.RationalFamilyPowerProgram

/-! # Fixed-order error propagation for finite powers and reciprocals -/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

theorem unit_bound {Primary Body : Type*} (order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |unit (Scalar := ℝ) order arity colors centers| ≤ 1 := by
  unfold unit
  split_ifs <;> norm_num

theorem power_bound {Primary Body : Type*} (order : ℕ) (table : Table ℝ Primary Body order)
    (bound scale : ℝ) (hb : 0 ≤ bound) (hs : 1 ≤ scale)
    (hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * bound ≤ scale)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound) (count : ℕ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |power order table count arity colors centers| ≤ scale^count := by
  induction count generalizing arity colors centers with
  | zero => simpa only [power, pow_zero] using unit_bound order arity colors centers
  | succ count ih =>
      have h := product_bound order (power order table count) table (scale^count) bound
        (pow_nonneg (by linarith) _) hb ih htable arity colors centers
      simp only [Fintype.card_eq_nat_card] at h
      apply h.trans
      have hm := mul_le_mul_of_nonneg_left hscale (pow_nonneg (by linarith : 0 ≤ scale) count)
      rw [pow_succ scale count]
      convert hm using 1
      ring

def growth (order : ℕ) (bound error : ℝ) : ℝ :=
  1 + (Nat.card (TruncatedArity order) : ℝ)^2 * (bound + error + 1)

theorem growth_ge_one (order : ℕ) (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) :
    1 ≤ growth order bound error := by
  unfold growth
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (by positivity))

theorem growth_scale (order : ℕ) (bound error : ℝ) :
    (Nat.card (TruncatedArity order) : ℝ)^2 * (bound + error + 1) ≤ growth order bound error := by
  unfold growth
  linarith

theorem power_error {Primary Body : Type*} (order : ℕ) (table computed : Table ℝ Primary Body order)
    (bound error scale : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hs : 1 ≤ scale)
    (hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * (bound + error + 1) ≤ scale)
    (htable : ∀ arity colors centers, |table arity colors centers| ≤ bound)
    (herror : ∀ arity colors centers, |computed arity colors centers - table arity colors centers| ≤ error)
    (count : ℕ) (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |power order computed count arity colors centers - power order table count arity colors centers| ≤
      count * error * scale^count := by
  have hn : 0 ≤ (Nat.card (TruncatedArity order) : ℝ)^2 := sq_nonneg _
  have hbase : (Nat.card (TruncatedArity order) : ℝ)^2 * bound ≤ scale :=
    (mul_le_mul_of_nonneg_left (show bound ≤ bound+error+1 by linarith) hn).trans hscale
  have hstep : (Nat.card (TruncatedArity order) : ℝ)^2 * (bound+error) ≤ scale :=
    (mul_le_mul_of_nonneg_left (show bound+error ≤ bound+error+1 by linarith) hn).trans hscale
  have hcount : (Nat.card (TruncatedArity order) : ℝ)^2 ≤ scale := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ bound+error+1 by linarith) hn
    rw [mul_one] at h
    exact h.trans hscale
  induction count generalizing arity colors centers with
  | zero => simp only [power, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ count ih =>
      have hp := power_bound order table bound scale hb hs hbase htable count
      have h := product_error order (power order table count) (power order computed count) table computed
        (scale^count) bound (count*error*scale^count) error
        (by positivity) hb (by positivity) he hp htable ih herror arity colors centers
      simp only [Fintype.card_eq_nat_card] at h
      apply h.trans
      have hfirst := mul_le_mul_of_nonneg_left hstep
        (show 0 ≤ (count:ℝ)*error*scale^count by positivity)
      have hsecond := mul_le_mul_of_nonneg_left hcount (show 0 ≤ error*scale^count by positivity)
      calc
        _ = ((count:ℝ)*error*scale^count) *
            ((Nat.card (TruncatedArity order):ℝ)^2*(bound+error)) +
            (error*scale^count) * (Nat.card (TruncatedArity order):ℝ)^2 := by ring
        _ ≤ ((count:ℝ)*error*scale^count)*scale + (error*scale^count)*scale := add_le_add hfirst hsecond
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring


end
end CurrentAFT.RationalFamilyProductProgram

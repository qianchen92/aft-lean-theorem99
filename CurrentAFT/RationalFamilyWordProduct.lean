import CurrentAFT.RationalActualFamilyApproximation
import CurrentAFT.RationalFamilyPowerBounds

/-! # Products of distinct local coefficient tables in an explicitly ordered word -/
namespace CurrentAFT.RationalFamilyWordProduct
open AFT ActualControls ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current {Scalar Primary Body : Type*} [Field Scalar] (order : ℕ) :
    (count : ℕ) → (Fin count → Table Scalar Primary Body order) → Table Scalar Primary Body order
  | 0, _ => unit order
  | count+1, tables => product order (current order count (fun index => tables index.succ)) (tables 0)

noncomputable section
open scoped Classical
local instance wordProductFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem current_cast {Primary Body : Type*} (order count : ℕ) (tables : Fin count → Table ℚ Primary Body order) :
    realTable order (current order count tables) = current order count (fun index => realTable order (tables index)) := by
  induction count with
  | zero => exact unit_cast order
  | succ count ih => simp only [current, product_cast, ih]

theorem current_actual (security order count : ℕ) (families : Fin count → BackgroundFamilies.ActualFamily security order) :
    current order count (fun index arity => (families index arity).val) =
      fun arity => ((∏ index, families index) arity).val := by
  induction count with
  | zero => simpa only [current, Fin.prod_univ_zero] using unit_actual (ProposalPrimary.primaryLaw security) (bodyReference security) order
  | succ count ih =>
    rw [current, ih, product_actual, Fin.prod_univ_succ]
    have hm : (∏ index : Fin count, families index.succ) * families 0 =
        families 0 * (∏ index : Fin count, families index.succ) := mul_comm _ _
    change (fun arity => (((∏ index : Fin count, families index.succ) * families 0) arity).val) =
      (fun arity => ((families 0 * (∏ index : Fin count, families index.succ)) arity).val)
    rw [hm]

theorem interpret_current (security order count : ℕ) (tables : Fin count → Table ℚ ℕ ℕ order) :
    RationalActualFamilyApproximation.interpret security order (current order count tables) =
      current order count (fun index => RationalActualFamilyApproximation.interpret security order (tables index)) := by
  induction count with
  | zero =>
    unfold RationalActualFamilyApproximation.interpret current
    rw [unit_cast, pullback_unit]
  | succ count ih =>
    rw [current, RationalActualFamilyApproximation.interpret_product, ih]
    rfl

theorem current_bound {Primary Body : Type*} (order count : ℕ) (tables : Fin count → Table ℝ Primary Body order)
    (bound scale : ℝ) (hb : 0 ≤ bound) (hs : 1 ≤ scale)
    (hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * bound ≤ scale)
    (htable : ∀ index arity colors centers, |tables index arity colors centers| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |current order count tables arity colors centers| ≤ scale^count := by
  induction count generalizing arity colors centers with
  | zero => simpa only [current, pow_zero] using unit_bound order arity colors centers
  | succ count ih =>
    have ht := ih (fun index => tables index.succ) (fun index => htable index.succ)
    have h := product_bound order (current order count (fun index => tables index.succ)) (tables 0)
      (scale^count) bound (by positivity) hb ht (htable 0) arity colors centers
    simp only [Fintype.card_eq_nat_card] at h
    apply h.trans
    have hm := mul_le_mul_of_nonneg_left hscale (pow_nonneg (by linarith : 0 ≤ scale) count)
    rw [pow_succ scale count]
    convert hm using 1
    ring

theorem current_error {Primary Body : Type*} (order count : ℕ) (tables computed : Fin count → Table ℝ Primary Body order)
    (bound error scale : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hs : 1 ≤ scale)
    (hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * (bound + error + 1) ≤ scale)
    (htable : ∀ index arity colors centers, |tables index arity colors centers| ≤ bound)
    (herror : ∀ index arity colors centers, |computed index arity colors centers - tables index arity colors centers| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |current order count computed arity colors centers - current order count tables arity colors centers| ≤
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
  | zero => simp only [current, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ count ih =>
    have ht := current_bound order count (fun index => tables index.succ) bound scale hb hs hbase (fun index => htable index.succ)
    have hi := ih (fun index => tables index.succ) (fun index => computed index.succ)
      (fun index => htable index.succ) (fun index => herror index.succ)
    have h := product_error order (current order count (fun index => tables index.succ))
      (current order count (fun index => computed index.succ)) (tables 0) (computed 0)
      (scale^count) bound (count*error*scale^count) error (by positivity) hb (by positivity) he
      ht (htable 0) hi (herror 0) arity colors centers
    simp only [Fintype.card_eq_nat_card] at h
    apply h.trans
    have hfirst := mul_le_mul_of_nonneg_left hstep (show 0 ≤ (count : ℝ)*error*scale^count by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hcount (show 0 ≤ error*scale^count by positivity)
    calc
      _ = ((count : ℝ)*error*scale^count) * ((Nat.card (TruncatedArity order) : ℝ)^2*(bound+error)) +
          (error*scale^count) * (Nat.card (TruncatedArity order) : ℝ)^2 := by ring
      _ ≤ ((count : ℝ)*error*scale^count)*scale + (error*scale^count)*scale := add_le_add hfirst hsecond
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring

end
end CurrentAFT.RationalFamilyWordProduct

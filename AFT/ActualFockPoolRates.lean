import AFT.ActualJointFock
import AFT.JointFockActivity

/-! # The actual local Fock scales retain both original pool normalizations -/
namespace AFT.V7Calibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualFockPoolRatesFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualRolePoolCapacity (parameter : ℕ) (role : Bool) : ℕ :=
  if role then Parameters.legs parameter else Parameters.bodies parameter

def actualRoleRateFactor (parameter : ℕ) (role : Bool) : ℝ :=
  if role then Real.sqrt primaryFockEnergyConstant else 32 * (parameter : ℝ) ^ 2

/-- Any actually retained subpool has at most the original pool size. Its
inverse square root dominates the primary lambda^-15 rate, and the body
lambda^-28 rate after exactly the prescribed radius lambda². -/
theorem actualRoleBound_le_pool_rate (parameter : ℕ) (hp : 2 ≤ parameter)
    (role : Bool) (pool : ℕ) (hpool : 0 < pool) (hcapacity : pool ≤ actualRolePoolCapacity parameter role) :
    actualRoleBound parameter role ≤ actualRoleRateFactor parameter role * (1 / Real.sqrt pool) := by
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hroot : 0 < Real.sqrt (pool : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hpool)
  rw [mul_one_div, le_div_iff₀ hroot]
  cases role with
  | true =>
    simp only [actualRoleBound, actualRoleRateFactor, actualRolePoolCapacity, if_true] at *
    have hleg : (Parameters.legs parameter : ℝ) = (parameter : ℝ) ^ 30 := by
      simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]
    have hpBound : (pool : ℝ) ≤ (parameter : ℝ) ^ 30 := by exact (show (pool : ℝ) ≤ Parameters.legs parameter by exact_mod_cast hcapacity).trans_eq hleg
    have hs : Real.sqrt (pool : ℝ) ≤ (parameter : ℝ) ^ 15 := (Real.sqrt_le_iff).2 ⟨by positivity, by convert hpBound using 1; ring⟩
    calc
      _ ≤ (Real.sqrt primaryFockEnergyConstant / (parameter : ℝ) ^ 15) * (parameter : ℝ) ^ 15 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp
  | false =>
    simp only [actualRoleBound, actualRoleRateFactor, actualRolePoolCapacity, Bool.false_eq_true, if_false] at *
    have hd : (Parameters.dimension parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 60 := by
      exact_mod_cast (show Parameters.dimension parameter ≤ 2 * parameter ^ 60 by
        simpa only [Parameters.security_eq parameter hp] using (Parameters.dimension_bounds parameter).2)
    have hb : Parameters.bodies parameter ≤ Parameters.dimension parameter := Nat.sub_le _ _
    have hpoolBound : (pool : ℝ) ≤ 2 * (parameter : ℝ) ^ 60 :=
      (show (pool : ℝ) ≤ Parameters.dimension parameter by exact_mod_cast hcapacity.trans hb).trans hd
    have hs : Real.sqrt (pool : ℝ) ≤ 2 * (parameter : ℝ) ^ 30 := (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith [pow_nonneg hx.le 60]⟩
    calc
      _ ≤ (16 / (parameter : ℝ) ^ 28) * (2 * (parameter : ℝ) ^ 30) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp; ring

/-- The full mixed input activity controls all joint response rates with no
loss beyond one radius lambda² for each body input. -/
theorem actual_role_product_energy_le_activity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hp : 2 ≤ parameter) (count : ℕ) (role : Fin count → Bool) (pool : Fin count → ℕ)
    (hpool : ∀ index, 0 < pool index)
    (hcapacity : ∀ index, pool index ≤ actualRolePoolCapacity parameter (role index))
    (kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ) :
    (∏ index, actualRoleBound parameter (role index) ^ 2) *
      (FiniteDist.independent (fun index => actualRoleInput cutoffScale parameter beta (role index))).l2Sq kernel ≤
    (∏ index, actualRoleRateFactor parameter (role index) ^ 2) *
      MixedKernel.activity (fun index => 1 / Real.sqrt (pool index))
        (fun index => actualRoleInput cutoffScale parameter beta (role index)) kernel ^ 2 := by
  apply JointPhysicalChannel.product_energy_le_activity_square
    (fun index => 1 / Real.sqrt (pool index)) (fun index => actualRoleRateFactor parameter (role index))
    (fun index => actualRoleBound parameter (role index))
    (fun index => actualRoleInput cutoffScale parameter beta (role index)) kernel
    (fun index => by positivity) (fun index => by dsimp only [actualRoleRateFactor]; split_ifs <;> positivity)
    (fun index => by dsimp only [actualRoleBound]; split_ifs <;> positivity)
    (fun index => actualRoleBound_le_pool_rate parameter hp (role index) (pool index) (hpool index) (hcapacity index))

end
end AFT.V7Calibration

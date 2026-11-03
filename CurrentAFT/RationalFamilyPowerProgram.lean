import CurrentAFT.RationalFamilyProductBounds
import CurrentAFT.GradedInverse

/-! # Fixed-degree rational powers and finite inverse tables

Only powers up to the fixed calibration order occur in the inverse and
binomial programs. Population powers are represented by binomial coefficients,
rather than by a population-length sequence of approximate multiplications.
-/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def unit {Scalar Primary Body : Type*} [Zero Scalar] [One Scalar] (order : ℕ) : Table Scalar Primary Body order :=
  fun arity _ _ => if arity = zeroArity order then 1 else 0

def power {Scalar Primary Body : Type*} [Field Scalar] (order : ℕ)
    (table : Table Scalar Primary Body order) : ℕ → Table Scalar Primary Body order
  | 0 => unit order
  | count+1 => product order (power order table count) table

def reciprocal {Scalar Primary Body : Type*} [Field Scalar] (order : ℕ)
    (table : Table Scalar Primary Body order) : Table Scalar Primary Body order :=
  fun arity colors centers => ∑ count ∈ Finset.range (order+1),
    power order (unit order - table) count arity colors centers

def binomial {Scalar Primary Body : Type*} [Field Scalar] (order population : ℕ)
    (table : Table Scalar Primary Body order) : Table Scalar Primary Body order :=
  fun arity colors centers => ∑ count ∈ Finset.range (order+1),
    (population.choose count : Scalar) * power order table count arity colors centers

noncomputable section
open scoped Classical
local instance powerFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem unit_cast {Primary Body : Type*} (order : ℕ) :
    realTable order (unit (Scalar := ℚ) (Primary := Primary) (Body := Body) order) = unit order := by
  funext arity colors centers
  simp only [realTable, unit, apply_ite, Rat.cast_one, Rat.cast_zero]
  split_ifs <;> rfl

theorem power_cast {Primary Body : Type*} (order : ℕ) (table : Table ℚ Primary Body order) (count : ℕ) :
    realTable order (power order table count) = power order (realTable order table) count := by
  induction count with
  | zero => exact unit_cast order
  | succ count ih => simp only [power, product_cast, ih]

theorem reciprocal_cast {Primary Body : Type*} (order : ℕ) (table : Table ℚ Primary Body order) :
    realTable order (reciprocal order table) = reciprocal order (realTable order table) := by
  have hsub : realTable order (unit order - table) = unit order - realTable order table := by
    funext arity colors centers
    simp only [realTable, Pi.sub_apply, Rat.cast_sub]
    exact congrArg (fun value => value - (table arity colors centers : ℝ))
      (congrFun (congrFun (congrFun (unit_cast (Primary := Primary) (Body := Body) order) arity) colors) centers)
  funext arity colors centers
  simp only [realTable, reciprocal, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro count _
  change realTable order (power order (unit order - table) count) arity colors centers = _
  rw [power_cast, hsub]

theorem binomial_cast {Primary Body : Type*} (order population : ℕ) (table : Table ℚ Primary Body order) :
    realTable order (binomial order population table) = binomial order population (realTable order table) := by
  funext arity colors centers
  simp only [realTable, binomial, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]
  apply Finset.sum_congr rfl
  intro count _
  congr 1
  exact congrFun (congrFun (congrFun (power_cast order table count) arity) colors) centers

theorem unit_actual {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    unit (Scalar := ℝ) (Primary := Primary) (Body := Body) order =
      fun arity => ((1 : KernelFamily primary body order) arity).val := by
  funext arity colors centers
  unfold unit
  change _ = ((familyUnit primary body order) arity).val colors centers
  by_cases heq : arity = zeroArity order
  · subst arity
    simp only [familyUnit, Pi.single_eq_same, if_true, scalarUnit]
  · simp only [familyUnit, Pi.single_eq_of_ne heq, heq, if_false, Submodule.coe_zero, Pi.zero_apply]

theorem power_actual {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order count : ℕ)
    (family : KernelFamily primary body order) :
    power order (fun arity => (family arity).val) count = fun arity => ((family^count) arity).val := by
  induction count with
  | zero => exact unit_actual primary body order
  | succ count ih =>
      rw [power, ih, product_actual, pow_succ]
      rfl

theorem reciprocal_actual {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) :
    reciprocal order (fun arity => (family arity).val) =
      fun arity => (backgroundInverse primary body order family arity).val := by
  have hsub : unit order - (fun arity => (family arity).val) =
      fun arity => ((1 - family : KernelFamily primary body order) arity).val := by
    rw [unit_actual primary body order]
    rfl
  funext arity colors centers
  simp only [reciprocal, hsub, power_actual, backgroundInverse, Finset.sum_apply, Submodule.coe_sum]

theorem power_zero_above {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) (hzero : family (zeroArity order) = 0)
    (count : ℕ) (hcount : order < count) : family^count = 0 := by
  have h := vanishesBelow_pow primary body order family
    (vanishesBelow_one_of_zero primary body order family hzero) count
  funext arity
  exact h arity (by have := arity.property; omega)

theorem binomial_family_sum {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order population : ℕ)
    (family : KernelFamily primary body order) (hzero : family (zeroArity order) = 0) :
    (1 + family)^population =
      ∑ count ∈ Finset.range (order+1), population.choose count • family^count := by
  have hfull : (1 + family)^population =
      ∑ count ∈ Finset.range (population+1), population.choose count • family^count := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro count _
    rw [one_pow, mul_one, nsmul_eq_mul, mul_comm]
  rw [hfull]
  by_cases hle : population ≤ order
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro count _ hnot
    have hlarge : population < count := by simpa only [Finset.mem_range, not_lt] using hnot
    rw [Nat.choose_eq_zero_of_lt hlarge, zero_nsmul]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro count _ hnot
    have hlarge : order < count := by simpa only [Finset.mem_range, not_lt] using hnot
    rw [power_zero_above primary body order family hzero count hlarge, smul_zero]

theorem binomial_actual {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order population : ℕ)
    (family : KernelFamily primary body order) (hzero : family (zeroArity order) = 0) :
    binomial order population (fun arity => (family arity).val) =
      fun arity => (((1 + family)^population) arity).val := by
  rw [binomial_family_sum primary body order population family hzero]
  funext arity colors centers
  simp only [binomial, power_actual, Finset.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro count _
  change _ = population.choose count • (((family^count) arity).val colors centers)
  rw [nsmul_eq_mul]

end
end CurrentAFT.RationalFamilyProductProgram

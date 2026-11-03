import CurrentAFT.RationalFamilyPowerProgram

/-! # Coefficient-table arithmetic commutes with palette representation -/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable {Scalar Primary Body Primary' Body' : Type*}

def pullback (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (table : Table Scalar Primary Body order) : Table Scalar Primary' Body' order :=
  fun arity colors centers => table arity (primary ∘ colors) (body ∘ centers)

theorem pullback_unit [Zero Scalar] [One Scalar] (order : ℕ)
    (primary : Primary' → Primary) (body : Body' → Body) :
    pullback order primary body (unit (Scalar := Scalar) order) = unit order := rfl

theorem pullback_sub [Sub Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (first second : Table Scalar Primary Body order) :
    pullback order primary body (first - second) = pullback order primary body first - pullback order primary body second := rfl

theorem pullback_product [Field Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (first second : Table Scalar Primary Body order) :
    pullback order primary body (product order first second) =
      product order (pullback order primary body first) (pullback order primary body second) := by
  funext arity colors centers
  unfold pullback product
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  split_ifs <;> rfl

theorem pullback_power [Field Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (table : Table Scalar Primary Body order) (count : ℕ) :
    pullback order primary body (power order table count) =
      power order (pullback order primary body table) count := by
  induction count with
  | zero => exact pullback_unit order primary body
  | succ count ih => simp only [power, pullback_product, ih]

theorem pullback_reciprocal [Field Scalar] (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (table : Table Scalar Primary Body order) :
    pullback order primary body (reciprocal order table) = reciprocal order (pullback order primary body table) := by
  funext arity colors centers
  unfold reciprocal
  change (∑ count ∈ Finset.range (order+1),
    pullback order primary body (power order (unit order-table) count) arity colors centers) = _
  simp only [pullback_power, pullback_sub, pullback_unit]

theorem pullback_binomial [Field Scalar] (order population : ℕ)
    (primary : Primary' → Primary) (body : Body' → Body) (table : Table Scalar Primary Body order) :
    pullback order primary body (binomial order population table) =
      binomial order population (pullback order primary body table) := by
  funext arity colors centers
  unfold binomial
  change (∑ count ∈ Finset.range (order+1), (population.choose count : Scalar) *
    pullback order primary body (power order table count) arity colors centers) = _
  simp only [pullback_power]

theorem pullback_cast (order : ℕ) (primary : Primary' → Primary) (body : Body' → Body)
    (table : Table ℚ Primary Body order) :
    realTable order (pullback order primary body table) = pullback order primary body (realTable order table) := rfl

end CurrentAFT.RationalFamilyProductProgram

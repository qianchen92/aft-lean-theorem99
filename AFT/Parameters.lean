import Mathlib

/-!
# The fixed parameter powers of reference V7

The modulus is an actual prime selected using Bertrand's theorem. No prime
existence premise is attached to the subsequent population inequalities.
Small security parameters use `max 2 parameter`; this agrees with every
eventual statement of Section 9.
-/

namespace AFT.Parameters

noncomputable section

def security (parameter : ℕ) : ℕ := max 2 parameter

theorem security_ge_two (parameter : ℕ) : 2 ≤ security parameter := le_max_left _ _

theorem security_eq (parameter : ℕ) (hp : 2 ≤ parameter) : security parameter = parameter :=
  max_eq_right hp

private theorem prime_exists (parameter : ℕ) :
    ∃ modulus : ℕ, modulus.Prime ∧ security parameter ^ 40 < modulus ∧
      modulus ≤ 2 * security parameter ^ 40 :=
  Nat.exists_prime_lt_and_le_two_mul _
    (pow_ne_zero _ (show security parameter ≠ 0 by have := security_ge_two parameter; omega))

/-- A prime in the exact power interval specified in Section 9. -/
noncomputable def modulus (parameter : ℕ) : ℕ := Nat.find (prime_exists parameter)

theorem modulus_spec (parameter : ℕ) : (modulus parameter).Prime ∧
    security parameter ^ 40 < modulus parameter ∧
      modulus parameter ≤ 2 * security parameter ^ 40 := Nat.find_spec (prime_exists parameter)

theorem modulus_prime (parameter : ℕ) : (modulus parameter).Prime := (modulus_spec parameter).1

theorem modulus_bounds (parameter : ℕ) :
    security parameter ^ 40 ≤ modulus parameter ∧
      modulus parameter ≤ 2 * security parameter ^ 40 :=
  ⟨(modulus_spec parameter).2.1.le, (modulus_spec parameter).2.2⟩

def meanDensity (parameter : ℕ) : ℕ := security parameter ^ 20
def dimension (parameter : ℕ) : ℕ := modulus parameter * meanDensity parameter
def legs (parameter : ℕ) : ℕ := security parameter ^ 30
def bodies (parameter : ℕ) : ℕ := dimension parameter - 2 * legs parameter
def anchorWidth (parameter : ℕ) : ℕ := security parameter ^ 32
def safeMargin (parameter : ℕ) : ℕ := 20 * security parameter ^ 2
def safeSize (parameter : ℕ) : ℕ := modulus parameter - 2 * safeMargin parameter

theorem dimension_bounds (parameter : ℕ) :
    security parameter ^ 60 ≤ dimension parameter ∧
      dimension parameter ≤ 2 * security parameter ^ 60 := by
  have h := modulus_bounds parameter
  have heq : security parameter ^ 40 * security parameter ^ 20 =
      security parameter ^ 60 := by rw [← pow_add]
  constructor
  · exact heq ▸ Nat.mul_le_mul_right (security parameter ^ 20) h.1
  · have hh := Nat.mul_le_mul_right (security parameter ^ 20) h.2
    simpa only [Nat.mul_assoc, heq, dimension, meanDensity] using hh

theorem four_legs_le_dimension (parameter : ℕ) : 4 * legs parameter ≤ dimension parameter := by
  have hm : 4 ≤ security parameter ^ 30 := by
    have hh := Nat.pow_le_pow_left (security_ge_two parameter) 30
    omega
  have heq : security parameter ^ 60 = legs parameter * legs parameter := by
    unfold legs
    rw [← pow_add]
  have hd := (dimension_bounds parameter).1
  rw [heq] at hd
  exact (Nat.mul_le_mul_right (legs parameter) hm).trans hd

theorem bodies_positive (parameter : ℕ) : 0 < bodies parameter := by
  have hm : 0 < legs parameter := pow_pos (lt_of_lt_of_le (by decide : 0 < 2)
    (security_ge_two parameter)) _
  have hd := four_legs_le_dimension parameter
  unfold bodies
  omega

theorem population_identity (parameter : ℕ) :
    bodies parameter + 2 * legs parameter = dimension parameter := by
  have h := four_legs_le_dimension parameter
  exact Nat.sub_add_cancel (by omega)

theorem legs_le_half_bodies (parameter : ℕ) : 2 * legs parameter ≤ bodies parameter := by
  have h := four_legs_le_dimension parameter
  unfold bodies
  omega

/-- The public anchor intervals fit with the exact six-width clearance. -/
theorem anchor_clearance (parameter : ℕ) : 6 * anchorWidth parameter + 1 ≤ modulus parameter := by
  have hp : 6 ≤ security parameter ^ 8 := by
    have h := Nat.pow_le_pow_left (security_ge_two parameter) 8
    omega
  have hq := (modulus_spec parameter).2.1
  have heq : security parameter ^ 40 = security parameter ^ 8 * anchorWidth parameter := by
    unfold anchorWidth
    rw [← pow_add]
  rw [heq] at hq
  have h := Nat.mul_le_mul_right (anchorWidth parameter) hp
  omega

/-- The actual safe-center palette is nonempty, even at the global fallback
parameter; this uses the specified modulus power rather than an assumption. -/
theorem safeSize_positive (parameter : ℕ) : 0 < safeSize parameter := by
  have hp : 40 ≤ security parameter ^ 38 := by
    have h := Nat.pow_le_pow_left (security_ge_two parameter) 38
    omega
  have hq := (modulus_spec parameter).2.1
  have heq : security parameter ^ 40 = security parameter ^ 38 * security parameter ^ 2 := by
    rw [← pow_add]
  rw [heq] at hq
  have h := Nat.mul_le_mul_right (security parameter ^ 2) hp
  unfold safeSize safeMargin
  omega

end

end AFT.Parameters

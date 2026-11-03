import Mathlib

/-!
# The current manuscript's public parameter family

These definitions follow `sec:df-parameter-choice`, not the frozen V7
parameters. They are independent of the accuracy order. The least-prime
choice and its polynomial size are proved using Bertrand's theorem.
This file does not claim a polynomial-time implementation of prime search
or of the affine sampler.
-/

namespace CurrentAFT.Parameters

def base (security : ℕ) : ℕ := security + 2
def scale (security : ℕ) : ℕ := base security ^ 8
def primeThreshold (security : ℕ) : ℕ := 2 ^ 16 * scale security ^ 8

theorem base_ge_two (security : ℕ) : 2 ≤ base security := by simp [base]

theorem base_pos (security : ℕ) : 0 < base security := by simp [base]

theorem primeThreshold_eq (security : ℕ) :
    primeThreshold security = 65536 * base security ^ 64 := by
  simp [primeThreshold, scale, ← pow_mul]

/- The checked witness contains both the actual least-prime search value
and its defining properties. Its opacity prevents the kernel from trying
to evaluate that search while comparing finite-alphabet instances. -/
private opaque leastPrimeWitness (security : ℕ) :
    {prime : ℕ // (primeThreshold security ≤ prime ∧ prime.Prime) ∧
      ∀ candidate, primeThreshold security ≤ candidate → candidate.Prime → prime ≤ candidate} :=
  ⟨Nat.find (Nat.exists_infinite_primes (primeThreshold security)),
    Nat.find_spec (Nat.exists_infinite_primes (primeThreshold security)),
    fun _ hthreshold hprime => Nat.find_min' _ ⟨hthreshold, hprime⟩⟩

def modulus (security : ℕ) : ℕ := (leastPrimeWitness security).val

theorem modulus_spec (security : ℕ) :
    primeThreshold security ≤ modulus security ∧ (modulus security).Prime :=
  (leastPrimeWitness security).property.1

theorem modulus_least (security prime : ℕ)
    (hthreshold : primeThreshold security ≤ prime) (hprime : prime.Prime) :
    modulus security ≤ prime :=
  (leastPrimeWitness security).property.2 prime hthreshold hprime

/-- The opaque checked representation has exactly the original search
value, not merely some prime meeting a size bound. -/
theorem modulus_eq_find (security : ℕ) :
    modulus security = Nat.find (Nat.exists_infinite_primes (primeThreshold security)) := by
  apply Nat.le_antisymm
  · exact modulus_least security _
      (Nat.find_spec (Nat.exists_infinite_primes (primeThreshold security))).1
      (Nat.find_spec (Nat.exists_infinite_primes (primeThreshold security))).2
  · exact Nat.find_min' _ (modulus_spec security)

theorem modulus_upper (security : ℕ) :
    modulus security ≤ 2 * primeThreshold security := by
  have hthreshold : primeThreshold security ≠ 0 := by
    rw [primeThreshold_eq]
    exact ne_of_gt (mul_pos (by norm_num) (pow_pos (base_pos security) _))
  obtain ⟨prime, hprime, hlower, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (primeThreshold security) hthreshold
  exact (modulus_least security prime hlower.le hprime).trans hupper

theorem modulus_bounds (security : ℕ) :
    65536 * base security ^ 64 ≤ modulus security ∧
      modulus security ≤ 131072 * base security ^ 64 := by
  constructor
  · simpa only [primeThreshold_eq] using (modulus_spec security).1
  · have h := modulus_upper security
    rw [primeThreshold_eq] at h
    omega

def bodySize (security : ℕ) : ℕ := modulus security * scale security ^ 12
def legCount (security : ℕ) : ℕ := scale security ^ 16
def dimension (security : ℕ) : ℕ := bodySize security + 2 * legCount security
def sourceWidth (security : ℕ) : ℕ := base security
def sourceCutoff (security : ℕ) : ℕ := base security ^ 2
def safeMargin (security : ℕ) : ℕ := 3 * sourceCutoff security
def anchorWidth (security : ℕ) : ℕ := scale security ^ 6

theorem bodySize_eq (security : ℕ) :
    bodySize security = modulus security * base security ^ 96 := by
  simp [bodySize, scale, ← pow_mul]

theorem legCount_eq (security : ℕ) : legCount security = base security ^ 128 := by
  simp [legCount, scale, ← pow_mul]

/-- Explicit polynomial bounds, with constants independent of accuracy. -/
theorem dimension_bounds (security : ℕ) :
    65536 * base security ^ 160 ≤ dimension security ∧
      dimension security ≤ 131074 * base security ^ 160 := by
  have hmod := modulus_bounds security
  have hpowers : base security ^ 128 ≤ base security ^ 160 :=
    Nat.pow_le_pow_right (by have := base_ge_two security; omega) (by omega)
  have hbody := Nat.mul_le_mul_right (base security ^ 96) hmod.1
  have hbodyUpper := Nat.mul_le_mul_right (base security ^ 96) hmod.2
  have hproduct : base security ^ 64 * base security ^ 96 = base security ^ 160 := by
    rw [← pow_add]
  rw [mul_assoc, hproduct] at hbody hbodyUpper
  simp only [dimension, bodySize_eq, legCount_eq]
  constructor <;> omega

/-- Calibration, unlike public parameters, may depend on the fixed order. -/
def calibrationOrder (accuracyOrder : ℕ) : ℕ := 4 * accuracyOrder + 267

theorem calibrationOrder_exponent (accuracyOrder : ℕ) :
    ((calibrationOrder accuracyOrder : ℕ) + 1 : ℝ) / 4 =
      (accuracyOrder : ℝ) + 67 := by
  simp [calibrationOrder]
  ring

theorem accuracy_exponent (accuracyOrder order : ℕ)
    (horder : 4 * accuracyOrder + 267 ≤ order) :
    (64 : ℝ) - ((order : ℝ) + 1) / 4 ≤ -(accuracyOrder : ℝ) - 3 := by
  have h : (4 : ℝ) * accuracyOrder + 267 ≤ order := by exact_mod_cast horder
  linarith

/-- The main Fourier term for the chosen order has three spare powers.
This proves the exponent calculation, not the physical Fourier estimate. -/
theorem fourier_term_bound (security accuracyOrder : ℕ) :
    (modulus security : ℝ) * (base security : ℝ) ^
        (-(((calibrationOrder accuracyOrder : ℕ) + 1 : ℝ) / 4)) ≤
      131072 / (base security : ℝ) ^ (accuracyOrder + 3) := by
  have hb : (0 : ℝ) < base security := by exact_mod_cast base_pos security
  have hm : (modulus security : ℝ) ≤ 131072 * (base security : ℝ) ^ 64 := by
    exact_mod_cast (modulus_bounds security).2
  rw [calibrationOrder_exponent]
  have hexp : (accuracyOrder : ℝ) + 67 = ((accuracyOrder + 67 : ℕ) : ℝ) := by norm_num
  rw [hexp, Real.rpow_neg hb.le, Real.rpow_natCast, ← div_eq_mul_inv]
  calc
    _ ≤ (131072 * (base security : ℝ) ^ 64) /
        (base security : ℝ) ^ (accuracyOrder + 67) := by
      exact div_le_div_of_nonneg_right hm (pow_nonneg hb.le _)
    _ = _ := by
      have hsum : accuracyOrder + 67 = 64 + (accuracyOrder + 3) := by omega
      rw [hsum, pow_add]
      field_simp

-- Residue alphabets depend on this least-prime value. Keep the search
-- abstract during automatic typeclass normalization; explicit rewriting
-- with its definition remains available.
attribute [irreducible] modulus

end CurrentAFT.Parameters

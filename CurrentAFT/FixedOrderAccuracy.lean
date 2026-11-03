import CurrentAFT.Parameters

/-!
# The final fixed-order error arithmetic

The public family is fixed before choosing the accuracy order. Its actual
modulus bound and calibration order leave three spare inverse powers in the
Fourier term. For each fixed constant, these powers absorb that constant;
a negligible remainder and the prescribed decreasing numerical budget then
give the requested eventual accuracy.

This file proves only this arithmetic and its quantifiers. It does not prove
the actual calibrated weight's negligible remainder, produce a sampler, or
verify the implementation of the numerical budget. Increasing the exponent
used to bound the remainder does not change that remainder function.
-/

namespace CurrentAFT

open Filter
open scoped Topology

/-- Inverse powers use the current public base `security + 2`. -/
noncomputable def inversePower (security order : ℕ) : ℝ :=
  1 / (Parameters.base security : ℝ) ^ order

theorem inversePower_nonneg (security order : ℕ) : 0 ≤ inversePower security order := by
  unfold inversePower
  positivity

theorem inversePower_eq_rpow (security order : ℕ) :
    inversePower security order = (Parameters.base security : ℝ) ^ (-(order : ℝ)) := by
  have hbase : (0 : ℝ) ≤ Parameters.base security := by positivity
  rw [Real.rpow_neg hbase, Real.rpow_natCast]
  simp only [inversePower, one_div]

/-- A fixed multiplicative Fourier constant is absorbed by one of the three
spare powers. The threshold depends on that fixed constant, not on a sampler
that observes the hidden source. -/
theorem fourier_error_le_inversePower_eventually (order : ℕ) (constant : ℝ)
    (hconstant : 0 ≤ constant) :
    ∀ᶠ security : ℕ in atTop,
      constant * (Parameters.modulus security : ℝ) * (Parameters.base security : ℝ) ^
          (-(((Parameters.calibrationOrder order : ℕ) + 1 : ℝ) / 4)) ≤
        inversePower security (order + 2) := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (131072 * constant)
  filter_upwards [eventually_ge_atTop threshold] with security hsecurity
  have hbase : (0 : ℝ) < Parameters.base security := by
    exact_mod_cast Parameters.base_pos security
  have hlarge : 131072 * constant ≤ (Parameters.base security : ℝ) := by
    apply hthreshold.trans
    exact_mod_cast (show threshold ≤ Parameters.base security by
      dsimp [Parameters.base]
      omega)
  calc
    _ = constant * ((Parameters.modulus security : ℝ) * (Parameters.base security : ℝ) ^
        (-(((Parameters.calibrationOrder order : ℕ) + 1 : ℝ) / 4))) := by ring
    _ ≤ constant * (131072 / (Parameters.base security : ℝ) ^ (order + 3)) :=
      mul_le_mul_of_nonneg_left (Parameters.fourier_term_bound security order) hconstant
    _ = (131072 * constant) / (Parameters.base security : ℝ) ^ (order + 3) := by ring
    _ ≤ (Parameters.base security : ℝ) /
        (Parameters.base security : ℝ) ^ (order + 3) :=
      div_le_div_of_nonneg_right hlarge (pow_nonneg hbase.le _)
    _ = inversePower security (order + 2) := by
      have hexponent : order + 3 = (order + 2) + 1 := by omega
      rw [hexponent, pow_succ]
      unfold inversePower
      field_simp

/-- Three errors at order `order + 2` fit within one error at order `order`
because the actual base is always at least two. -/
theorem three_inversePower_le (security order : ℕ) :
    3 * inversePower security (order + 2) ≤ inversePower security order := by
  have hbase : (0 : ℝ) < Parameters.base security := by
    exact_mod_cast Parameters.base_pos security
  have htwo : (2 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast Parameters.base_ge_two security
  have hpower : (0 : ℝ) < (Parameters.base security : ℝ) ^ order := pow_pos hbase _
  calc
    _ = 3 / (Parameters.base security : ℝ) ^ (order + 2) := by
      unfold inversePower
      ring
    _ ≤ 1 / (Parameters.base security : ℝ) ^ order := by
      rw [pow_add]
      apply (div_le_div_iff₀ (mul_pos hpower (pow_pos hbase 2)) hpower).mpr
      nlinarith [sq_nonneg ((Parameters.base security : ℝ) - 2)]

/-- The final error implication for a fixed accuracy order. The same fixed
remainder function satisfies every eventual inverse-power bound; it is not
replaced when the proof selects the bound at `order + 2`.

This statement is valid even at order zero; the manuscript uses positive
orders. It assumes no construction existence or running-time conclusion. -/
theorem fixed_order_accuracy_eventually (order : ℕ) (constant : ℝ)
    (hconstant : 0 ≤ constant) (remainder numerical : ℕ → ℝ)
    (hremainder : ∀ boundOrder : ℕ, ∀ᶠ security : ℕ in atTop,
      remainder security ≤ inversePower security boundOrder)
    (hnumerical : ∀ᶠ security : ℕ in atTop,
      numerical security ≤ (1 / 4 : ℝ) * inversePower security (order + 2)) :
    ∀ᶠ security : ℕ in atTop,
      constant * (Parameters.modulus security : ℝ) * (Parameters.base security : ℝ) ^
          (-(((Parameters.calibrationOrder order : ℕ) + 1 : ℝ) / 4)) +
          remainder security + numerical security ≤ (security : ℝ) ^ (-(order : ℝ)) := by
  filter_upwards [fourier_error_le_inversePower_eventually order constant hconstant,
    hremainder (order + 2), hnumerical, eventually_ge_atTop 1]
    with security hfourier hremainderAt hnumericalAt hsecurity
  have hsecurityPos : (0 : ℝ) < security := by
    exact_mod_cast (show 0 < security by omega)
  have hbudget : numerical security ≤ inversePower security (order + 2) := by
    exact hnumericalAt.trans (by nlinarith [inversePower_nonneg security (order + 2)])
  calc
    _ ≤ 3 * inversePower security (order + 2) := by linarith
    _ ≤ inversePower security order := three_inversePower_le security order
    _ ≤ 1 / (security : ℝ) ^ order := by
      apply one_div_le_one_div_of_le (pow_pos hsecurityPos _)
      apply pow_le_pow_left₀ hsecurityPos.le
      exact_mod_cast (show security ≤ Parameters.base security by
        dsimp [Parameters.base]
        omega)
    _ = (security : ℝ) ^ (-(order : ℝ)) := by
      rw [Real.rpow_neg hsecurityPos.le, Real.rpow_natCast]
      simp only [one_div]

/-- The same implication with real-power notation for all accuracy budgets,
as in the current manuscript. Neither the public parameters nor the fixed
remainder change when the requested negligible bound is chosen. -/
theorem fixed_order_accuracy_eventually_rpow (order : ℕ) (constant : ℝ)
    (hconstant : 0 ≤ constant) (remainder numerical : ℕ → ℝ)
    (hremainder : ∀ boundOrder : ℕ, ∀ᶠ security : ℕ in atTop,
      remainder security ≤ (Parameters.base security : ℝ) ^ (-(boundOrder : ℝ)))
    (hnumerical : ∀ᶠ security : ℕ in atTop,
      numerical security ≤ (1 / 4 : ℝ) * (Parameters.base security : ℝ) ^
        (-((order + 2 : ℕ) : ℝ))) :
    ∀ᶠ security : ℕ in atTop,
      constant * (Parameters.modulus security : ℝ) * (Parameters.base security : ℝ) ^
          (-(((Parameters.calibrationOrder order : ℕ) + 1 : ℝ) / 4)) +
          remainder security + numerical security ≤ (security : ℝ) ^ (-(order : ℝ)) := by
  apply fixed_order_accuracy_eventually order constant hconstant remainder numerical
  · simpa only [inversePower_eq_rpow] using hremainder
  · simpa only [inversePower_eq_rpow] using hnumerical

end CurrentAFT

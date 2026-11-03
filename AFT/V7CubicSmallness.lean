import AFT.V7BlockBudgets

/-! # The physical doubled-radius Fock conditions hold for the V7 parameters -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts
open scoped BigOperators Classical Topology

noncomputable section

local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

/-- All population, normalization, and degree budgets are numerical
consequences of the explicit V7 powers. -/
theorem cubic_numeric_budgets (parameter : ℕ) (hlarge : 100000000 ≤ parameter) :
    let scale := Real.sqrt 2 * ((parameter : ℝ) ^ 2 / Real.sqrt (Parameters.dimension parameter))
    scale ^ 2 * ((Parameters.legs parameter : ℝ) * (100000 * (parameter : ℝ) ^ 22) +
      (Parameters.bodies parameter - Parameters.legs parameter : ℕ) * (10944 / (parameter : ℝ) ^ 38)) ≤ 1 / 8 ∧
    128 * Parameters.legs parameter *
      (scale ^ 2 * (1256 * (parameter : ℝ) ^ 15) +
        Real.sqrt (Parameters.bodies parameter) * scale ^ 3 * (1256 * (parameter : ℝ) ^ 15)) ≤ 1 / 2 := by
  let x : ℝ := parameter
  have hxlarge : 100000000 ≤ x := by dsimp only [x]; exact_mod_cast hlarge
  have hx1 : 1 ≤ x := by linarith
  have hx : 0 < x := by linarith
  have hp : 2 ≤ parameter := by omega
  have hd0 : (0 : ℝ) < Parameters.dimension parameter := by
    have hh := (Parameters.dimension_bounds parameter).1
    have hs : 0 < Parameters.security parameter ^ 60 := pow_pos (by have := Parameters.security_ge_two parameter; omega) _
    exact_mod_cast hs.trans_le hh
  have hd : x ^ 60 ≤ (Parameters.dimension parameter : ℝ) ∧ (Parameters.dimension parameter : ℝ) ≤ 2 * x ^ 60 := by
    dsimp only [x]
    exact_mod_cast (show parameter ^ 60 ≤ Parameters.dimension parameter ∧ Parameters.dimension parameter ≤ 2 * parameter ^ 60 by
      simpa only [Parameters.security_eq parameter hp] using Parameters.dimension_bounds parameter)
  have hm : (Parameters.legs parameter : ℝ) = x ^ 30 := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow, x]
  have hnb : (Parameters.bodies parameter : ℝ) ≤ 2 * x ^ 60 := by
    have hh : (Parameters.bodies parameter : ℝ) ≤ Parameters.dimension parameter := by
      exact_mod_cast (show Parameters.bodies parameter ≤ Parameters.dimension parameter by unfold Parameters.bodies; omega)
    exact hh.trans hd.2
  have hf : ((Parameters.bodies parameter - Parameters.legs parameter : ℕ) : ℝ) ≤ 2 * x ^ 60 := by
    have hh : ((Parameters.bodies parameter - Parameters.legs parameter : ℕ) : ℝ) ≤ Parameters.bodies parameter := by
      exact_mod_cast Nat.sub_le (Parameters.bodies parameter) (Parameters.legs parameter)
    exact hh.trans hnb
  have hroot : x ^ 30 ≤ Real.sqrt (Parameters.dimension parameter) :=
    (Real.le_sqrt (by positivity) hd0.le).mpr (by convert hd.1 using 1; ring)
  have hnbroot : Real.sqrt (Parameters.bodies parameter) ≤ 2 * x ^ 30 :=
    (Real.sqrt_le_left (by positivity)).mpr (by nlinarith only [hnb, pow_nonneg hx.le 60])
  let scale := Real.sqrt 2 * (x ^ 2 / Real.sqrt (Parameters.dimension parameter))
  have hs : 0 ≤ scale := by dsimp only [scale]; positivity
  have hscale : scale ≤ 2 / x ^ 28 := by
    calc
      _ ≤ 2 * (x ^ 2 / x ^ 30) := by
        apply mul_le_mul (Real.sqrt_two_lt_three_halves.le.trans (by norm_num))
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hroot) (by positivity) (by norm_num)
      _ = _ := by field_simp
  have hpow (degree : ℕ) (hd : 1 ≤ degree) : x ≤ x ^ degree := by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 hd
  constructor
  · change scale ^ 2 * _ ≤ _
    calc
      _ ≤ (2 / x ^ 28) ^ 2 * ((x ^ 30) * (100000 * x ^ 22) + (2 * x ^ 60) * (10944 / x ^ 38)) := by
        rw [hm]
        gcongr
      _ = 400000 / x ^ 4 + 87552 / x ^ 34 := by field_simp; ring
      _ ≤ 400000 / x + 87552 / x := add_le_add
        (div_le_div_of_nonneg_left (by norm_num) hx (hpow 4 (by norm_num)))
        (div_le_div_of_nonneg_left (by norm_num) hx (hpow 34 (by norm_num)))
      _ = 487552 / x := by ring
      _ ≤ 1 / 8 := (div_le_iff₀ hx).mpr (by linarith)
  · change (128 : ℝ) * (Parameters.legs parameter : ℝ) *
      (scale ^ 2 * (1256 * x ^ 15) + Real.sqrt (Parameters.bodies parameter) * scale ^ 3 * (1256 * x ^ 15)) ≤ 1 / 2
    rw [hm]
    calc
      _ ≤ 128 * x ^ 30 *
          ((2 / x ^ 28) ^ 2 * (1256 * x ^ 15) +
            (2 * x ^ 30) * (2 / x ^ 28) ^ 3 * (1256 * x ^ 15)) := by gcongr
      _ = 643072 / x ^ 11 + 2572288 / x ^ 9 := by field_simp; ring
      _ ≤ 643072 / x + 2572288 / x := add_le_add
        (div_le_div_of_nonneg_left (by norm_num) hx (hpow 11 (by norm_num)))
        (div_le_div_of_nonneg_left (by norm_num) hx (hpow 9 (by norm_num)))
      _ = 3215360 / x := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hx).mpr (by linarith)

/-- The true physical independent blocks satisfy every doubled-radius
cubic/Fock condition at radius `λ²`, uniformly over all legal root words and
all legal masked realizations of the common queue. -/
theorem actual_cubic_conditions_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root queue : blockIndex parameter → ℤ,
      (∀ index, |root index| ≤ (v7RootCutoff parameter : ℤ)) →
      (∀ index, |queue index| ≤ (queueCutoff parameter : ℤ)) →
      CubicBlockConditions (blockSlots parameter) (actualReferenceLaw cutoffScale parameter (beta parameter))
        (actualBlockFamily cutoffScale parameter (beta parameter) root queue)
        (Parameters.dimension parameter) (Parameters.bodies parameter) ((parameter : ℝ) ^ 2) := by
  filter_upwards [actual_normalized_block_budgets_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 100000000] with parameter hb hlarge root queue hr hq
  let scale := Real.sqrt 2 * ((parameter : ℝ) ^ 2 / Real.sqrt (Parameters.dimension parameter))
  have hs : 0 ≤ scale := by dsimp only [scale]; positivity
  have hactual := hb root queue hr hq scale hs
  have hnum := cubic_numeric_budgets parameter hlarge
  apply CubicBlockConditions_of_scaled
  · exact (blockIndex_card parameter).le
  · exact hactual.1.trans hnum.1
  · exact hactual.2.trans hnum.2

end

end AFT.V7Calibration

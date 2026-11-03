import Mathlib

/-!
# Explicit eventual meaning of negligible error

The security parameter is a natural number. Every inverse-polynomial order
has its own threshold; no claim is made about arbitrary accuracy at a fixed
parameter.
-/

namespace AFT

open Filter
open scoped Topology

/-- The usual eventual inverse-polynomial definition, including absolute
values so the definition also applies to signed error expressions. -/
def Negligible (error : ℕ → ℝ) : Prop :=
  ∀ order : ℕ, ∀ᶠ parameter : ℕ in atTop,
    |error parameter| ≤ 1 / (parameter : ℝ) ^ order

/-- A positive stretched exponential dominates every real power. -/
theorem stretched_exponential_tendsto (power exponent rate : ℝ)
    (hexponent : 0 < exponent) (hrate : 0 < rate) :
    Tendsto (fun parameter : ℝ => parameter ^ power *
      Real.exp (-rate * parameter ^ exponent)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (power / exponent) rate hrate).comp (tendsto_rpow_atTop hexponent)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with parameter hp
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hp, mul_div_cancel₀ power hexponent.ne']

/-- Polynomially many stretched-exponential errors are genuinely negligible,
with arbitrary fixed positive exponent, including the leg exponent `1/4`. -/
theorem negligible_polynomial_stretched_exponential
    (constant : ℝ) (degree : ℕ) (exponent rate : ℝ)
    (hconstant : 0 ≤ constant) (hexponent : 0 < exponent) (hrate : 0 < rate) :
    Negligible (fun parameter => constant * (parameter : ℝ) ^ degree *
      Real.exp (-rate * (parameter : ℝ) ^ exponent)) := by
  intro order
  have hreal := (stretched_exponential_tendsto (degree + order : ℕ) exponent rate
    hexponent hrate).const_mul constant
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ parameter : ℕ in atTop,
      constant * ((parameter : ℝ) ^ (degree + order : ℕ) *
        Real.exp (-rate * (parameter : ℝ) ^ exponent)) < 1 := by
    simpa only [Function.comp_apply, mul_zero, Real.rpow_natCast] using
      hnat.eventually (gt_mem_nhds (show constant * (0 : ℝ) < 1 by simp))
  filter_upwards [hsmall, eventually_ge_atTop 1] with parameter hs hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hnonneg : 0 ≤ constant * (parameter : ℝ) ^ degree *
      Real.exp (-rate * (parameter : ℝ) ^ exponent) := by positivity
  rw [abs_of_nonneg hnonneg, le_div_iff₀ (pow_pos hp' order)]
  rw [pow_add] at hs
  nlinarith [hs]

/-- An eventual pointwise upper bound transfers negligible error. -/
theorem Negligible.of_eventually_le {error bound : ℕ → ℝ} (hbound : Negligible bound)
    (h : ∀ᶠ parameter in atTop, |error parameter| ≤ |bound parameter|) :
    Negligible error := by
  intro order
  filter_upwards [h, hbound order] with parameter hp hq
  exact hp.trans hq

theorem Negligible.comp_add {error : ℕ → ℝ} (h : Negligible error) (offset : ℕ) :
    Negligible (fun parameter => error (parameter + offset)) := by
  intro order
  have ht : Tendsto (fun parameter : ℕ => parameter + offset) atTop atTop :=
    tendsto_atTop_mono (fun parameter => Nat.le_add_right parameter offset) tendsto_id
  filter_upwards [ht.eventually (h order), eventually_ge_atTop 1] with parameter he hp
  apply he.trans
  apply one_div_le_one_div_of_le
  · exact pow_pos (by exact_mod_cast (show 0 < parameter by omega)) order
  · exact pow_le_pow_left₀ (Nat.cast_nonneg parameter) (by exact_mod_cast
      (show parameter ≤ parameter + offset by omega)) order

theorem Negligible.add {left right : ℕ → ℝ} (hl : Negligible left)
    (hr : Negligible right) : Negligible (fun parameter => left parameter + right parameter) := by
  intro order
  filter_upwards [hl (order + 1), hr (order + 1), eventually_ge_atTop 2]
    with parameter hl' hr' hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have htwo : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
  apply (abs_add_le _ _).trans ((add_le_add hl' hr').trans ?_)
  rw [pow_succ, ← add_div]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hp' order) hp') (pow_pos hp' order)).mpr
  nlinarith [pow_pos hp' order]

theorem Negligible.mul_polynomial {error : ℕ → ℝ} (h : Negligible error) (degree : ℕ) :
    Negligible (fun parameter => (parameter : ℝ) ^ degree * error parameter) := by
  intro order
  filter_upwards [h (degree + order), eventually_ge_atTop 1] with parameter he hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (parameter : ℝ) ^ degree)]
  calc
    _ ≤ (parameter : ℝ) ^ degree * (1 / (parameter : ℝ) ^ (degree + order)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [pow_add]; field_simp

/-- The growing exponent `population ≥ parameter` makes any base bounded by
`1 / parameter` negligible, even with a fixed polynomial prefactor. -/
theorem negligible_growing_power (degree : ℕ) (base : ℕ → ℝ) (population : ℕ → ℕ)
    (hbase0 : ∀ᶠ parameter in atTop, 0 ≤ base parameter)
    (hbase : ∀ᶠ parameter in atTop, base parameter ≤ 1 / (parameter : ℝ))
    (hpopulation : ∀ᶠ parameter in atTop, parameter ≤ population parameter) :
    Negligible (fun parameter => (parameter : ℝ) ^ degree *
      base parameter ^ population parameter) := by
  intro order
  filter_upwards [hbase0, hbase, hpopulation, eventually_ge_atTop (max 2 (degree + order))]
    with parameter hb0 hb hp hparameter
  have htwo : 2 ≤ parameter := (le_max_left _ _).trans hparameter
  have hdeg : degree + order ≤ population parameter :=
    ((le_max_right _ _).trans hparameter).trans hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hone : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hi0 : 0 ≤ 1 / (parameter : ℝ) := by positivity
  have hi1 : 1 / (parameter : ℝ) ≤ 1 := (div_le_one hp').mpr hone
  have hpowers : base parameter ^ population parameter ≤
      (1 / (parameter : ℝ)) ^ (degree + order) :=
    (pow_le_pow_left₀ hb0 hb _).trans (pow_le_pow_of_le_one hi0 hi1 hdeg)
  rw [abs_of_nonneg (by positivity : 0 ≤ (parameter : ℝ) ^ degree *
    base parameter ^ population parameter)]
  calc
    _ ≤ (parameter : ℝ) ^ degree * (1 / (parameter : ℝ)) ^ (degree + order) :=
      mul_le_mul_of_nonneg_left hpowers (by positivity)
    _ = _ := by simp only [div_pow, one_pow, pow_add]; field_simp

end AFT

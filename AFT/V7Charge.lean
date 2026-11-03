import AFT.V7ReferenceLaws
import AFT.BodyTypeParameters
import AFT.ActualOutputChannels
import AFT.Negligible

/-! # Actual safe-center charge mixing for the V7 family -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

attribute [local instance] actualModulusNeZero

def actualAnchorLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  (actualPrimaryLaw cutoffScale parameter beta).mix fun input =>
    ⟨fun output => publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) input output.val,
      fun _ => publicAnchorKernel_nonneg _ _ _ _, (actual_anchor_safe_mass parameter input).1⟩

@[simp] theorem actualAnchorLaw_weight (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (output : Fin (Parameters.modulus parameter)) :
    (actualAnchorLaw cutoffScale parameter beta).weight output =
      anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (actualPrimaryLaw cutoffScale parameter beta).weight output.val := rfl

theorem actualCoreLaw_uniformDeviation (parameter : ℕ) :
    (actualCoreLaw parameter).uniformDeviation =
      4 * Parameters.safeMargin parameter / (Parameters.modulus parameter : ℝ) := by
  rw [actualCoreLaw, FiniteDist.uniformSafe_deviation, Fintype.card_fin, safePalette_card]
  have hm : 2 * Parameters.safeMargin parameter ≤ Parameters.modulus parameter := by
    have hh := safeMargin_quarter parameter
    omega
  simp only [Parameters.safeSize, Nat.cast_sub hm, Nat.cast_mul, Nat.cast_ofNat]
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  field_simp
  ring

/-- The actual compensated body law has a vanishing L1 deviation from
palette uniform, with no assumption about anchor concentration. -/
theorem actual_body_uniformDeviation_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (actualBodyLaw cutoffScale parameter (beta parameter)).uniformDeviation ≤
        84 / (parameter : ℝ) ^ 30 := by
  filter_upwards [actual_reference_laws_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hlaws hp
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hd : 0 ≤ bodyCompensation parameter cutoffScale := by
    unfold bodyCompensation
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale (by omega))).le)
      (Nat.cast_nonneg _)
  have hformula (color) : (actualBodyLaw cutoffScale parameter (beta parameter)).weight color =
      (1 + bodyCompensation parameter cutoffScale) * (actualCoreLaw parameter).weight color -
        bodyCompensation parameter cutoffScale * (actualAnchorLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hlaws.2.1, actualAnchorLaw_weight, hlaws.1]
    rfl
  have hh := FiniteDist.compensated_uniformDeviation
    (actualBodyLaw cutoffScale parameter (beta parameter)) (actualCoreLaw parameter)
    (actualAnchorLaw cutoffScale parameter (beta parameter)) (bodyCompensation parameter cutoffScale) hd hformula
  rw [actualCoreLaw_uniformDeviation] at hh
  have hq : (parameter : ℝ)^40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (show parameter^40 ≤ Parameters.modulus parameter by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
  have hcore : 4 * Parameters.safeMargin parameter / (Parameters.modulus parameter : ℝ) ≤
      80 / (parameter : ℝ)^38 := by
    simp only [Parameters.safeMargin, Parameters.security_eq parameter hp, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    calc
      _ ≤ (4 * (20 * (parameter : ℝ)^2)) / (parameter : ℝ)^40 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hq
      _ = _ := by field_simp; norm_num
  have hpow : (parameter : ℝ)^30 ≤ (parameter : ℝ)^38 := pow_le_pow_right₀ hx1 (by omega)
  have hc := hcore.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow)
  have hcomp := bodyCompensation_coarse cutoffScale parameter hscale hp
  simp only [div_eq_mul_inv] at hh hc hcomp ⊢
  linarith only [hh, hc, hcomp]

theorem bodies_after_deletions_grow (cutoff : ℕ) :
    ∀ᶠ parameter : ℕ in atTop, parameter ≤ Parameters.bodies parameter - cutoff := by
  filter_upwards [eventually_ge_atTop (cutoff + 2)] with parameter hp
  have hp2 : 2 ≤ parameter := by omega
  have hdim : parameter ^ 60 ≤ Parameters.dimension parameter := by
    simpa only [Parameters.security_eq parameter hp2] using (Parameters.dimension_bounds parameter).1
  have hpop := Parameters.population_identity parameter
  have hlegs := Parameters.legs_le_half_bodies parameter
  have hbody : parameter ^ 60 ≤ 2 * Parameters.bodies parameter := by omega
  have hpow : parameter ^ 2 ≤ parameter ^ 60 := pow_le_pow_right₀ (by omega) (by omega)
  have hquad : 2 * (parameter + cutoff) ≤ parameter ^ 2 := by
    have hmul := Nat.mul_le_mul_left parameter hp
    have hmul' := Nat.mul_le_mul_right cutoff hp2
    nlinarith
  omega

theorem actual_body_uniformDeviation_inv_parameter_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (actualBodyLaw cutoffScale parameter (beta parameter)).uniformDeviation ≤ 1 / (parameter : ℝ) := by
  filter_upwards [actual_body_uniformDeviation_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 84]
    with parameter h hp
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hpow : (parameter : ℝ) ≤ (parameter : ℝ)^29 := by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (by omega : 1 ≤ 29)
  apply h.trans
  calc
    _ ≤ (parameter : ℝ)^29 / (parameter : ℝ)^30 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (show (84 : ℝ) ≤ parameter by exact_mod_cast hp).trans hpow
    _ = _ := by field_simp

/-- The finite charge-ratio budget is negligible after deleting any fixed
number of controlled centers. The center law is the actual V7 law. -/
theorem actual_charge_error_negligible (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter)
    (cutoff : ℕ) :
    Negligible (fun parameter => 4 * Parameters.modulus parameter *
      (actualBodyLaw cutoffScale parameter (beta parameter)).uniformDeviation ^
        (Parameters.bodies parameter - cutoff)) := by
  let base := fun parameter => (actualBodyLaw cutoffScale parameter (beta parameter)).uniformDeviation
  have hbase0 : ∀ᶠ parameter : ℕ in atTop, 0 ≤ base parameter :=
    Filter.Eventually.of_forall fun parameter => FiniteDist.uniformDeviation_nonneg _
  have hgrow := negligible_growing_power 43 base (fun parameter => Parameters.bodies parameter - cutoff)
    hbase0 (actual_body_uniformDeviation_inv_parameter_eventually cutoffScale hscale beta hbeta)
    (bodies_after_deletions_grow cutoff)
  apply hgrow.of_eventually_le
  filter_upwards [eventually_ge_atTop 2] with parameter hp
  have hx2 : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hq : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ)^40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter^40 by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).2)
  have hx3 : (8 : ℝ) ≤ (parameter : ℝ)^3 := by
    exact_mod_cast (show 8 ≤ parameter^3 by nlinarith [Nat.pow_le_pow_left hp 3])
  have hcoef : 4 * (Parameters.modulus parameter : ℝ) ≤ (parameter : ℝ)^43 := by
    have hh := mul_le_mul_of_nonneg_right hx3 (show 0 ≤ (parameter : ℝ)^40 by positivity)
    have heq : (parameter : ℝ)^3 * (parameter : ℝ)^40 = (parameter : ℝ)^43 := by ring
    rw [heq] at hh
    linarith
  rw [abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg (FiniteDist.uniformDeviation_nonneg _) _)), abs_of_nonneg (by
    exact mul_nonneg (by positivity) (pow_nonneg (FiniteDist.uniformDeviation_nonneg _) _))]
  exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg (FiniteDist.uniformDeviation_nonneg _) _)

/-- Every required charge has positive probability, and every realized
partial charge has the same negligible completion-ratio budget. -/
theorem actual_charge_ratio_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter)
    (cutoff : ℕ) :
    ∀ᶠ parameter in atTop, ∀ required partialCharge : Fin (Parameters.modulus parameter),
      let center := actualBodyLaw cutoffScale parameter (beta parameter)
      0 < (center.sumLaw (Parameters.bodies parameter)).weight required ∧
      |(center.sumLaw (Parameters.bodies parameter - cutoff)).weight (required - partialCharge) /
          (center.sumLaw (Parameters.bodies parameter)).weight required - 1| ≤
        4 * Parameters.modulus parameter * center.uniformDeviation ^ (Parameters.bodies parameter - cutoff) := by
  filter_upwards [(actual_charge_error_negligible cutoffScale hscale beta hbeta 0) 0,
    actual_body_uniformDeviation_inv_parameter_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hsmall ha hp required partialCharge
  let center := actualBodyLaw cutoffScale parameter (beta parameter)
  have ha0 := center.uniformDeviation_nonneg
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have ha1 : center.uniformDeviation ≤ 1 :=
    ha.trans ((div_le_one hx).mpr hx1)
  have hquarter : (Parameters.modulus parameter : ℝ) * center.uniformDeviation ^ Parameters.bodies parameter ≤ 1 / 4 := by
    simp only [Nat.sub_zero, pow_zero, div_one] at hsmall
    rw [abs_of_nonneg (by exact mul_nonneg (by positivity) (pow_nonneg ha0 _))] at hsmall
    dsimp only [center] at *
    linarith
  have hsmall' : (Fintype.card (Fin (Parameters.modulus parameter)) : ℝ) *
      center.uniformDeviation ^ Parameters.bodies parameter < 1 := by
    simp only [Fintype.card_fin]
    linarith
  have hh := center.charge_ratio_deviation (Parameters.bodies parameter) cutoff required partialCharge hsmall'
  refine ⟨hh.1, hh.2.trans ?_⟩
  simp only [Fintype.card_fin]
  have hpow : center.uniformDeviation ^ Parameters.bodies parameter ≤
      center.uniformDeviation ^ (Parameters.bodies parameter - cutoff) :=
    pow_le_pow_of_le_one ha0 ha1 (Nat.sub_le _ _)
  have hdenom : (1 : ℝ) / 2 ≤
      1 - Parameters.modulus parameter * center.uniformDeviation ^ Parameters.bodies parameter := by linarith
  calc
    _ ≤ ((Parameters.modulus parameter : ℝ) *
        (center.uniformDeviation ^ (Parameters.bodies parameter - cutoff) +
          center.uniformDeviation ^ Parameters.bodies parameter)) / (1 / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hq.le (add_nonneg (pow_nonneg ha0 _) (pow_nonneg ha0 _)))
        (by norm_num) hdenom
    _ ≤ ((Parameters.modulus parameter : ℝ) *
        (center.uniformDeviation ^ (Parameters.bodies parameter - cutoff) +
          center.uniformDeviation ^ (Parameters.bodies parameter - cutoff))) / (1 / 2) := by gcongr
    _ = _ := by ring

end

end AFT.V7Calibration

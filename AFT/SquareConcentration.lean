import AFT.FiniteConcentration

/-! # Exponential-square moments from finite sub-Gaussian estimates -/

namespace AFT.FiniteConcentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

noncomputable section

variable {Sample : Type*} [Fintype Sample]

/-- Gaussian linearization of a square exponential, with every finite
expectation and integrability condition retained explicitly. -/
theorem subGaussian_square_mgf (law : FiniteDist Sample) (value : Sample → ℝ)
    (variance parameter : ℝ) (hparameter : 0 ≤ parameter)
    (hsmall : 2 * parameter * variance < 1)
    (hmgf : ∀ test : ℝ, law.expectation (fun sample => Real.exp (test * value sample)) ≤
      Real.exp (variance * test ^ 2 / 2)) :
    law.expectation (fun sample => Real.exp (parameter * value sample ^ 2)) ≤
      (Real.sqrt (1 - 2 * parameter * variance))⁻¹ := by
  let gaussian := gaussianReal 0 (1 / 2)
  let integrand (sample : Sample) (point : ℝ) :=
    Real.exp ((2 * Real.sqrt parameter * value sample) * point)
  have hi (sample : Sample) : Integrable (integrand sample) gaussian :=
    integrable_exp_mul_gaussianReal _
  have heq (sample : Sample) : (∫ point, integrand sample point ∂gaussian) =
      Real.exp (parameter * value sample ^ 2) := by
    have hh := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1 / 2))
      (2 * Real.sqrt parameter * value sample)
    change (∫ point, integrand sample point ∂gaussian) = _ at hh
    rw [hh]
    congr 1
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, zero_mul, zero_add]
    nlinarith [Real.sq_sqrt hparameter]
  have hsum : Integrable (fun point => ∑ sample, law.weight sample * integrand sample point) gaussian :=
    integrable_finset_sum _ fun sample _ => (hi sample).const_mul _
  have hinterchange : law.expectation (fun sample => Real.exp (parameter * value sample ^ 2)) =
      ∫ point, (∑ sample, law.weight sample * integrand sample point) ∂gaussian := by
    rw [integral_finset_sum _ (fun sample _ => (hi sample).const_mul _)]
    unfold FiniteDist.expectation
    apply Finset.sum_congr rfl
    intro sample _
    rw [integral_const_mul, heq]
  rw [hinterchange]
  apply (integral_mono hsum (BlockFock.gaussian_square_exp_integrable (2 * parameter * variance) hsmall) ?_).trans_eq
    (BlockFock.gaussian_square_exp_integral (2 * parameter * variance))
  intro point
  have hh := hmgf (2 * Real.sqrt parameter * point)
  have hfun : (fun sample => Real.exp ((2 * Real.sqrt parameter * point) * value sample)) =
      (fun sample => integrand sample point) := by
    funext sample
    unfold integrand
    congr 1
    ring
  rw [hfun] at hh
  have hexp : variance * (2 * Real.sqrt parameter * point) ^ 2 / 2 =
      (2 * parameter * variance) * point ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hparameter]
    ring
  simpa only [hexp] using hh

end

end AFT.FiniteConcentration

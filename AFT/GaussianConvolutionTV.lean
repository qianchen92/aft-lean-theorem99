import AFT.CountableNormalizedTilt
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Total variation of the actual normalized integer Gaussian convolution -/
namespace AFT.GaussianSource
open scoped BigOperators
noncomputable section

private def convolutionPairsEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun point := (point.2,point.1-point.2)
  invFun point := (point.1+point.2,point.1)
  left_inv point := by ext <;> simp
  right_inv point := by ext <;> simp

private theorem summable_mass_pairs (left right : ℝ) (hl : 0<left) (hr : 0<right) :
    Summable (fun point : ℤ × ℤ => integerMass left point.2 * integerMass right (point.1-point.2)) := by
  have hp := (summable_integerMass left hl).mul_of_nonneg (summable_integerMass right hr)
    (integerMass_nonneg left hl) (integerMass_nonneg right hr)
  exact convolutionPairsEquiv.summable_iff.mpr hp

theorem summable_convolutionProbability (left right : ℝ) (hl : 0<left) (hr : 0<right) :
    Summable (convolutionProbability left right hl hr) := by
  have hp := summable_mass_pairs left right hl hr
  have hh := (summable_prod_of_nonneg (fun point =>
    mul_nonneg (integerMass_nonneg left hl point.2) (integerMass_nonneg right hr (point.1-point.2)))).mp hp
  change Summable (fun target => ∑' z : ℤ, (integerGaussian left hl z).toReal *
    (integerGaussian right hr (target-z)).toReal)
  simpa only [integerMass_eq_pmf left hl,integerMass_eq_pmf right hr] using hh.2

theorem convolutionProbability_sum (left right : ℝ) (hl : 0<left) (hr : 0<right) :
    (∑' target, convolutionProbability left right hl hr target)=1 := by
  have hp := summable_mass_pairs left right hl hr
  simp only [convolutionProbability,← integerMass_eq_pmf left hl,← integerMass_eq_pmf right hr]
  rw [← hp.tsum_prod]
  have he := convolutionPairsEquiv.tsum_eq
    (fun point : ℤ × ℤ => integerMass left point.1 * integerMass right point.2)
  simp only [convolutionPairsEquiv,Equiv.coe_fn_mk] at he
  rw [he]
  have hs := (summable_integerMass left hl).mul_of_nonneg (summable_integerMass right hr)
    (integerMass_nonneg left hl) (integerMass_nonneg right hr)
  rw [← (summable_integerMass left hl).tsum_mul_tsum (summable_integerMass right hr) hs,
    integerMass_sum left hl,integerMass_sum right hr,one_mul]

/-- The continuum theta approximation is compared with the normalized
Gaussian of width `sqrt(left²+right²)`, including both exact input normalizers. -/
theorem convolutionProbability_total_variation (left right : ℝ) (hl : 0<left) (hr : 0<right)
    (hsmall : thetaError (harmonicWidth left right)<1) :
    (∑' target, |convolutionProbability left right hl hr target -
      integerMass (sumWidth left right) target|)/2 ≤
        thetaError (harmonicWidth left right)/(1-thetaError (harmonicWidth left right)) := by
  let scale := harmonicWidth left right * realNormalizer (sumWidth left right) /
    (realNormalizer left * realNormalizer right)
  have hsum := sumWidth_pos left right hl hr
  have hnormalizer : 0<realNormalizer left*realNormalizer right := mul_pos
    (zero_lt_one.trans_le (realNormalizer_ge_one left hl))
    (zero_lt_one.trans_le (realNormalizer_ge_one right hr))
  have hscale : 0<scale := div_pos (mul_pos (harmonicWidth_pos left right hl hr)
    (zero_lt_one.trans_le (realNormalizer_ge_one _ hsum))) hnormalizer
  apply normalized_tilt_total_variation (integerMass (sumWidth left right))
    (convolutionProbability left right hl hr) (integerMass_nonneg _ hsum)
    (summable_integerMass _ hsum) (summable_convolutionProbability left right hl hr)
    (integerMass_sum _ hsum) (convolutionProbability_sum left right hl hr)
    scale (thetaError (harmonicWidth left right))
    (thetaError_nonneg _ (harmonicWidth_pos left right hl hr)) hsmall
  intro target
  have href : 0 < integerMass (sumWidth left right) target := div_pos (weight_pos _ _)
    (zero_lt_one.trans_le (realNormalizer_ge_one _ hsum))
  have he : scale*integerMass (sumWidth left right) target =
      harmonicWidth left right * weight (sumWidth left right) target /
        (realNormalizer left*realNormalizer right) := by
    dsimp [scale,integerMass]
    field_simp [(zero_lt_one.trans_le (realNormalizer_ge_one _ hsum)).ne']
  have ht := convolutionProbability_relative_error left right hl hr target
  rw [← he,div_sub_one (mul_pos hscale href).ne'] at ht
  rw [abs_div,abs_of_pos (mul_pos hscale href)] at ht
  exact (div_le_iff₀ (mul_pos hscale href)).mp ht |>.trans_eq (by ring)

end
end AFT.GaussianSource

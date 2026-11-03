import AFT.ActualPairedMatrixProgram
import AFT.ActualResponseProgram

/-! # Stable finite probability channel composition -/
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section

theorem bounded_product_error (a b c d firstError secondError : ℝ)
    (ha : |a| ≤ 1) (hd : |d| ≤ 1)
    (hfirst : |a-c| ≤ firstError) (hsecond : |b-d| ≤ secondError) :
    |a*b-c*d| ≤ firstError+secondError := by
  have he := V7Calibration.approximation_mul_error a b c d
  exact he.trans ((add_le_add
    ((mul_le_mul_of_nonneg_left hd (abs_nonneg _)).trans (by simpa only [mul_one] using hfirst))
    ((mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans (by simpa only [one_mul] using hsecond))))

theorem probability_expectation_perturbation {Source : Type*} [Fintype Source]
    (weight approximateWeight value approximateValue : Source → ℝ)
    (lawError kernelError : ℝ)
    (hw : ∀ source,0 ≤ weight source) (hm : ∑ source,weight source=1)
    (ha : ∀ source,|approximateValue source| ≤ 1)
    (he : ∑ source,|approximateWeight source-weight source| ≤ lawError)
    (hk : ∀ source,|approximateValue source-value source| ≤ kernelError) :
    |(∑ source,approximateWeight source*approximateValue source)-
      (∑ source,weight source*value source)| ≤ lawError+kernelError := by
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ source,(|approximateWeight source-weight source|+weight source*kernelError) := by
      apply Finset.sum_le_sum
      intro source _
      rw [show approximateWeight source*approximateValue source-weight source*value source=
        (approximateWeight source-weight source)*approximateValue source+
          weight source*(approximateValue source-value source) by ring]
      apply (abs_add_le _ _).trans
      simp only [abs_mul,abs_of_nonneg (hw source)]
      exact add_le_add ((mul_le_mul_of_nonneg_left (ha source) (abs_nonneg _)).trans_eq (mul_one _))
        (mul_le_mul_of_nonneg_left (hk source) (hw source))
    _ = (∑ source,|approximateWeight source-weight source|)+kernelError := by
      rw [Finset.sum_add_distrib,←Finset.sum_mul,hm,one_mul]
    _ ≤ _ := add_le_add he (le_refl kernelError)

end
end AFT.RationalNumerics

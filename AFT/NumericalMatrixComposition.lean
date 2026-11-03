import AFT.NumericalPairedScore
import AFT.MixedCoordinateProducts

/-! # Finite matrix composition with exact density weights and numerical error -/
namespace AFT.RationalNumerics
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

def densityMatrixEntry (reference : Color → ℝ) (operator : Module.End ℝ (Color → ℝ))
    (input output : Color) : ℝ :=
  reference input*LinearMap.toMatrix' operator output input/reference output

/-- The reference weight in each intermediate coordinate cancels exactly. -/
theorem densityMatrixEntry_comp (reference : Color → ℝ) (hpositive : ∀ color,reference color≠0)
    (first second : Module.End ℝ (Color → ℝ)) (input output : Color) :
    densityMatrixEntry reference (first.comp second) input output=
      ∑ middle,densityMatrixEntry reference first middle output*densityMatrixEntry reference second input middle := by
  unfold densityMatrixEntry
  rw [LinearMap.toMatrix'_comp]
  simp only [Matrix.mul_apply,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro middle _
  field_simp [hpositive middle,hpositive output]

/-- Two arbitrary finite matrix approximations compose with one palette
factor. Their entries may be signed and need not be Markov kernels. -/
theorem matrixComposition_error {Input Middle Output : Type*} [Fintype Middle]
    (first firstApprox : Middle → Output → ℝ) (second secondApprox : Input → Middle → ℝ)
    (firstBound secondBound firstError secondError : ℝ)
    (hfirst : 0 ≤ firstBound) (_hsecond : 0 ≤ secondBound)
    (heFirst : 0 ≤ firstError) (_heSecond : 0 ≤ secondError)
    (hA : ∀ middle output,|firstApprox middle output| ≤ firstBound)
    (hB : ∀ input middle,|second input middle| ≤ secondBound)
    (hAe : ∀ middle output,|firstApprox middle output-first middle output| ≤ firstError)
    (hBe : ∀ input middle,|secondApprox input middle-second input middle| ≤ secondError)
    (input : Input) (output : Output) :
    |(∑ middle,firstApprox middle output*secondApprox input middle)-
      (∑ middle,first middle output*second input middle)| ≤
      (Fintype.card Middle : ℝ)*(firstError*secondBound+firstBound*secondError) := by
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun middle _ => show
      |firstApprox middle output*secondApprox input middle-first middle output*second input middle| ≤
        firstError*secondBound+firstBound*secondError from by
    rw [show firstApprox middle output*secondApprox input middle-first middle output*second input middle=
      (firstApprox middle output-first middle output)*second input middle+
        firstApprox middle output*(secondApprox input middle-second input middle) by ring]
    apply (abs_add_le _ _).trans
    simp only [abs_mul]
    exact add_le_add (mul_le_mul (hAe _ _) (hB _ _) (abs_nonneg _) heFirst)
      (mul_le_mul (hA _ _) (hBe _ _) (abs_nonneg _) hfirst))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh

/-- The corresponding magnitude bound is independent of cancellation. -/
theorem matrixComposition_abs_le {Input Middle Output : Type*} [Fintype Middle]
    (first : Middle → Output → ℝ) (second : Input → Middle → ℝ)
    (firstBound secondBound : ℝ) (hfirst : 0 ≤ firstBound)
    (hA : ∀ middle output,|first middle output| ≤ firstBound)
    (hB : ∀ input middle,|second input middle| ≤ secondBound)
    (input : Input) (output : Output) :
    |∑ middle,first middle output*second input middle| ≤
      (Fintype.card Middle : ℝ)*firstBound*secondBound := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun middle _ => show
      |first middle output*second input middle| ≤ firstBound*secondBound from by
    rw [abs_mul]
    exact mul_le_mul (hA _ _) (hB _ _) (abs_nonneg _) hfirst)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hh

end
end AFT.RationalNumerics

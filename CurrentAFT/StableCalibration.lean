import Mathlib

/-!
# Stable finite-dimensional probability calibration

This is the common linear-response principle stated as
`thm:stable-finite-dimensional-calibration` in the current manuscript.
The reference evaluation may be rectangular or noninjective. Uniqueness
is asserted only for the full coefficient equation.

The proof obtains a lower norm bound from the perturbation estimate,
then uses finite dimensionality to obtain surjectivity. Application-specific
response factorizations, perturbation estimates, coefficient dimensions,
and computation costs are not asserted by this generic theorem.
-/

namespace CurrentAFT

namespace StableCalibration

variable {Coefficients : Type*} [NormedAddCommGroup Coefficients]
  [NormedSpace ℝ Coefficients]

/-- A perturbation of the identity with defect at most `theta < 1`
has the quantitative lower bound needed for stable inversion. -/
theorem coefficient_norm_le (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) (coefficient : Coefficients) :
    ‖coefficient‖ ≤ ‖operator coefficient‖ / (1 - theta) := by
  have hpoint : ‖(operator - ContinuousLinearMap.id ℝ Coefficients) coefficient‖ ≤
      theta * ‖coefficient‖ :=
    ((operator - ContinuousLinearMap.id ℝ Coefficients).le_opNorm coefficient).trans
      (mul_le_mul_of_nonneg_right hdefect (norm_nonneg coefficient))
  have htriangle : ‖coefficient‖ ≤ ‖operator coefficient‖ +
      ‖(operator - ContinuousLinearMap.id ℝ Coefficients) coefficient‖ := by
    calc
      ‖coefficient‖ =
          ‖operator coefficient -
            (operator - ContinuousLinearMap.id ℝ Coefficients) coefficient‖ := by simp
      _ ≤ _ := norm_sub_le _ _
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  nlinarith

theorem stable_operator_injective (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) : Function.Injective operator := by
  intro first second hequal
  have hnorm := coefficient_norm_le operator theta hdefect hgap (first - second)
  have hzero : operator (first - second) = 0 := by simp [map_sub, hequal]
  rw [hzero, norm_zero, zero_div] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

/-- Finite dimensionality turns the proved injectivity into
surjectivity; invertibility is not an input assumption. -/
theorem stable_operator_bijective [FiniteDimensional ℝ Coefficients]
    (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) : Function.Bijective operator := by
  have hinjective := stable_operator_injective operator theta hdefect hgap
  exact ⟨hinjective, LinearMap.surjective_of_injective (f := operator.toLinearMap) hinjective⟩

theorem coefficient_equation_existsUnique [FiniteDimensional ℝ Coefficients]
    (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) (target : Coefficients) :
    ∃! coefficient, operator coefficient = target := by
  have hbijective := stable_operator_bijective operator theta hdefect hgap
  obtain ⟨coefficient, hcoefficient⟩ := hbijective.2 target
  exact ⟨coefficient, hcoefficient,
    fun other hother => hbijective.1 (hother.trans hcoefficient.symm)⟩

/-- Stability is measured by the actual residual of any reference
coefficient, without requiring the target itself to be small. -/
theorem reference_correction_bound (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) (coefficient target : Coefficients)
    (hcoefficient : operator coefficient = target) (reference : Coefficients) :
    ‖coefficient - reference‖ ≤ ‖target - operator reference‖ / (1 - theta) := by
  simpa only [map_sub, hcoefficient] using
    coefficient_norm_le operator theta hdefect hgap (coefficient - reference)

variable {Weights Outputs : Type*} [AddCommGroup Weights] [Module ℝ Weights]
  [AddCommGroup Outputs] [Module ℝ Outputs]

/-- The current manuscript's stable calibration theorem. The
factorization is a relation among actual linear maps, and the reference
evaluation is not assumed to have an inverse. -/
theorem stable_finite_dimensional_calibration
    [FiniteDimensional ℝ Coefficients]
    (operator : Coefficients →L[ℝ] Coefficients)
    (synthesis : Coefficients →ₗ[ℝ] Weights) (response : Weights →ₗ[ℝ] Outputs)
    (evaluation : Coefficients →ₗ[ℝ] Outputs)
    (hresponse : response.comp synthesis = evaluation.comp operator.toLinearMap)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) (target : Coefficients) :
    ∃ coefficient,
      operator coefficient = target ∧
      (∀ other, operator other = target → other = coefficient) ∧
      response (synthesis coefficient) = evaluation target ∧
      ∀ reference, ‖coefficient - reference‖ ≤
        ‖target - operator reference‖ / (1 - theta) := by
  obtain ⟨coefficient, hcoefficient, hunique⟩ :=
    coefficient_equation_existsUnique operator theta hdefect hgap target
  refine ⟨coefficient, hcoefficient, hunique, ?_, ?_⟩
  · have hfactor := LinearMap.congr_fun hresponse coefficient
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hcoefficient] using hfactor
  · exact reference_correction_bound operator theta hdefect hgap coefficient target hcoefficient

/-- If a response coordinate is the actual mass functional, a target
mass of one gives normalized synthesized weight. No positivity claim
is inferred from this equation. -/
theorem calibrated_mass_one (synthesis : Coefficients →ₗ[ℝ] Weights)
    (response : Weights →ₗ[ℝ] Outputs) (evaluation : Coefficients →ₗ[ℝ] Outputs)
    (mass : Weights →ₗ[ℝ] ℝ) (massCoordinate : Outputs →ₗ[ℝ] ℝ)
    (hmass : massCoordinate.comp response = mass)
    (coefficient target : Coefficients)
    (hcalibrated : response (synthesis coefficient) = evaluation target)
    (htarget : massCoordinate (evaluation target) = 1) :
    mass (synthesis coefficient) = 1 := by
  rw [← LinearMap.congr_fun hmass (synthesis coefficient)]
  simpa only [LinearMap.comp_apply, hcalibrated] using htarget

end StableCalibration

end CurrentAFT

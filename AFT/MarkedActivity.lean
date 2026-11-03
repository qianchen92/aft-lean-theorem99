import AFT.MarkedSafePair
import AFT.MixedPair
import AFT.RepresentedPolynomial

/-! # The actual marked pair's mixed input activity, including all fibers -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def actualMarkedInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) where
  primaryOrder := 1
  bodyOrder := 1
  kernel := MixedKernel.pairKernel (actualMarkedSafeDensity cutoffScale parameter beta)

theorem actualMarkedInput_weight (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (primary body : FiniteDist (Fin (Parameters.modulus parameter))) (primaryPool bodyPool radius : ℝ) :
    RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius (actualMarkedInput cutoffScale parameter beta) =
      radius * MixedKernel.activity ![(Real.sqrt primaryPool)⁻¹, (Real.sqrt bodyPool)⁻¹]
        (MixedKernel.pairReference primary body) (MixedKernel.pairKernel (actualMarkedSafeDensity cutoffScale parameter beta)) := by
  have hrate : RepresentedPolynomial.inputRate primaryPool bodyPool (actualMarkedInput cutoffScale parameter beta) =
      ![(Real.sqrt primaryPool)⁻¹, (Real.sqrt bodyPool)⁻¹] := by funext i; fin_cases i <;> rfl
  have href : RepresentedPolynomial.inputReference primary body (actualMarkedInput cutoffScale parameter beta) =
      MixedKernel.pairReference primary body := by funext i; fin_cases i <;> rfl
  unfold RepresentedPolynomial.inputWeight MixedKernel.analyticActivity
  rw [hrate, href]
  simp only [actualMarkedInput, pow_one]
  rfl


/-- Every bound is instantiated at the actual marked safe kernel. The
probability arguments merely identify its actual calibrated references. -/
theorem actual_marked_input_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ (primary body : FiniteDist (Fin (Parameters.modulus parameter))),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      body.weight = actualBodyCenter cutoffScale parameter (beta parameter) →
      ∀ primaryPool bodyPool radius : ℝ, 0 ≤ radius →
      RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius
        (actualMarkedInput cutoffScale parameter (beta parameter)) ≤
      let firstRate := (Real.sqrt primaryPool)⁻¹
      let secondRate := (Real.sqrt bodyPool)⁻¹
      let full := Real.sqrt (markedPairSquareConstant cutoffScale) * (parameter : ℝ) ^ 4
      radius * firstRate * secondRate *
        (full + firstRate * full + secondRate * (72 * (parameter : ℝ) ^ 8) +
          firstRate * secondRate * (72 * (parameter : ℝ) ^ 8)) := by
  filter_upwards [actual_marked_safe_all_fibers cutoffScale hscale beta hbeta]
    with parameter h primary body hp hb primaryPool bodyPool radius hr
  dsimp only
  have hc : 0 ≤ markedPairSquareConstant cutoffScale := by
    unfold markedPairSquareConstant anchorSeedSquareConstant
    positivity
  have hsq : (Real.sqrt (markedPairSquareConstant cutoffScale) * (parameter : ℝ) ^ 4)^2 =
      markedPairSquareConstant cutoffScale * (parameter : ℝ) ^ 8 := by
    rw [mul_pow, Real.sq_sqrt hc]
    ring
  have hh := MixedKernel.pair_activity_le primary body (actualMarkedSafeDensity cutoffScale parameter (beta parameter))
    (Real.sqrt primaryPool)⁻¹ (Real.sqrt bodyPool)⁻¹
    (Real.sqrt (markedPairSquareConstant cutoffScale) * (parameter : ℝ) ^ 4)
    (Real.sqrt (markedPairSquareConstant cutoffScale) * (parameter : ℝ) ^ 4)
    (72 * (parameter : ℝ)^8) (72 * (parameter : ℝ)^8)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by rw [hp, hb, hsq]; exact h.2.2.1)
    (by intro x; rw [hb, hsq]; exact h.1 x)
    (by intro y; rw [hp]; exact h.2.2.2 y)
    h.2.1
  rw [actualMarkedInput_weight]
  exact (mul_le_mul_of_nonneg_left hh hr).trans_eq (by ring)

end
end AFT.V7Calibration

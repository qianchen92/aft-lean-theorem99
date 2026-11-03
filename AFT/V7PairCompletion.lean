import AFT.V7ActualPairResidual
import AFT.V7MixedInverse
import AFT.MixedCoordinateIteration

/-! # The exact actual two-primary completion with all mixed fibers -/

namespace AFT.V7Calibration

open GaussianSource SafeConvolution Filter MixedKernel
open scoped BigOperators Classical Topology

noncomputable section
attribute [local instance] actualModulusNeZero

/-- The completion is the literal result of applying the actual inverse
in each primary coordinate; its sign cancels the body output residual. -/
def actualPairCompletionInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ)) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) :=
  primaryPairSeed (inputIteration [0,1] (fun _ => operator.symm.toLinearMap)
    (pairReference (actualPrimaryLaw cutoffScale parameter beta) (actualPrimaryLaw cutoffScale parameter beta))
    (-(actualCanonicalPairResidualInput cutoffScale parameter beta).kernel))

/-- Exact actual response, including its activation and both density
weights; the final target uses the true calibrated reference. -/
theorem actualPairCompletionInput_exact (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ))
    (hop : operator.toLinearMap = actualResponse cutoffScale parameter)
    (hprimary : ∀ color, (actualPrimaryLaw cutoffScale parameter beta).weight color ≠ 0)
    (hactivation : v7Activation cutoffScale parameter ≠ 0)
    (word : Fin 2 → Fin (Parameters.modulus parameter)) :
    convolution (actualRootPair parameter).weight
      (actualCompactRootInput parameter 14 (actualPairCoreSeed parameter 14 (averagedInactivePair cutoffScale parameter))) (word 0,word 1) +
    v7Activation cutoffScale parameter ^ 2 *
      ((actualPrimaryLaw cutoffScale parameter beta).weight (word 0) * (actualPrimaryLaw cutoffScale parameter beta).weight (word 1)) *
      (inputIteration [1,0] (fun _ => actualResponse cutoffScale parameter)
        (pairReference (actualPrimaryLaw cutoffScale parameter beta) (actualPrimaryLaw cutoffScale parameter beta))
        (actualPairCompletionInput cutoffScale parameter beta operator).kernel) word =
      SafePair.canonicalPair (actualReferenceLaw cutoffScale parameter beta).weight
        (averagedInactivePair cutoffScale parameter) (word 0) (word 1) := by
  rw [← hop]
  have heq : inputIteration [1,0] (fun _ => operator.toLinearMap)
      (pairReference (actualPrimaryLaw cutoffScale parameter beta) (actualPrimaryLaw cutoffScale parameter beta))
      (actualPairCompletionInput cutoffScale parameter beta operator).kernel =
      -(actualCanonicalPairResidualInput cutoffScale parameter beta).kernel := by
    change partialInputOperator (1 : Fin 2) operator.toLinearMap (actualPrimaryLaw cutoffScale parameter beta).weight
      (partialInputOperator (0 : Fin 2) operator.toLinearMap (actualPrimaryLaw cutoffScale parameter beta).weight
        (partialInputOperator (0 : Fin 2) operator.symm.toLinearMap (actualPrimaryLaw cutoffScale parameter beta).weight
          (partialInputOperator (1 : Fin 2) operator.symm.toLinearMap (actualPrimaryLaw cutoffScale parameter beta).weight _))) = _
    rw [partialInputOperator_inverse _ _ _ hprimary, partialInputOperator_inverse _ _ _ hprimary]
    rfl
  rw [heq, Pi.neg_apply, actualCanonicalPairResidualInput_formula]
  field_simp [hprimary, hactivation]
  ring

/-- A single eventual threshold gives the exact inverse, its completed
pair certificate, and the full literal input activity cost. -/
theorem actual_pair_completion_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter) :
    ∀ᶠ parameter in atTop,
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = actualResponse cutoffScale parameter ∧
        (∀ color, (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color ≠ 0) ∧
        v7Activation cutoffScale parameter ≠ 0 ∧
        ∀ (body : FiniteDist (Fin (Parameters.modulus parameter))) (bodyPool radius : ℝ),
          RepresentedPolynomial.inputWeight (actualPrimaryLaw cutoffScale parameter (beta parameter)) body
            (pool parameter : ℝ) bodyPool radius (actualPairCompletionInput cutoffScale parameter (beta parameter) operator) ≤
          (Real.sqrt (pool parameter : ℝ))⁻¹ ^ 2 *
            (16 * (pairResidualMixedConstant cutoffScale + pairReferenceMixedConstant cutoffScale)) / (parameter : ℝ) ^ 2 := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_inverse_mixed_eventually (Slot := Fin 2) cutoffScale hscale beta pool htypical,
    actual_canonical_pair_residual_activity_eventually cutoffScale hscale beta pool htypical,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 1]
    with parameter hi hc hl hp hlarge
  obtain ⟨operator, hop, hi⟩ := hi
  refine ⟨operator, hop, (fun color => by rw [hl.1]; exact (hp.1 color).ne'),
    (activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale hlarge)).ne', ?_⟩
  intro body bodyPool radius
  rw [actualPairCompletionInput, primaryPairSeed_weight]
  let reference := pairReference (actualPrimaryLaw cutoffScale parameter (beta parameter))
    (actualPrimaryLaw cutoffScale parameter (beta parameter))
  let rates : Fin 2 → ℝ := ![(Real.sqrt (pool parameter : ℝ))⁻¹,(Real.sqrt (pool parameter : ℝ))⁻¹]
  have hrates (i : Fin 2) : 0 ≤ rates i := by fin_cases i <;> change 0 ≤ (Real.sqrt (pool parameter : ℝ))⁻¹ <;> positivity
  have hb (i : Fin 2) (_ : i ∈ [0,1]) (kernel : (Fin 2 → Fin (Parameters.modulus parameter)) → ℝ) :
      activity rates reference (partialInputOperator i operator.symm.toLinearMap (reference i).weight kernel) ≤
      4 * activity rates reference kernel := by
    apply hi reference rates i hrates
    · fin_cases i <;> rfl
    · fin_cases i <;> simp [rates, one_div]
  have hh := inputIteration_activity_le [0,1] (fun _ => operator.symm.toLinearMap) reference rates 4 (by norm_num) hb
    (-(actualCanonicalPairResidualInput cutoffScale parameter (beta parameter)).kernel)
  have hneg : activity rates reference (-(actualCanonicalPairResidualInput cutoffScale parameter (beta parameter)).kernel) =
      activity rates reference (actualCanonicalPairResidualInput cutoffScale parameter (beta parameter)).kernel := by
    simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using activity_smul rates reference
      (actualCanonicalPairResidualInput cutoffScale parameter (beta parameter)).kernel (-1)
  rw [hneg] at hh
  have hcost := hc body bodyPool radius
  rw [actualCanonicalPairResidualInput, primaryPairSeed_weight] at hcost
  exact (hh.trans (mul_le_mul_of_nonneg_left hcost (by positivity))).trans_eq (by norm_num; ring)

end
end AFT.V7Calibration

import AFT.V7PairReferenceActivity

/-! # The full residual for the actual reference-canonical inactive pair -/

namespace AFT.V7Calibration

open GaussianSource SafeConvolution Filter
open scoped BigOperators Classical Topology

noncomputable section
attribute [local instance] actualModulusNeZero

/-- Both literal corrections are retained before the primary inverse. -/
def actualCanonicalPairResidualInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) :=
  primaryPairSeed (fun word : Fin 2 → Fin (Parameters.modulus parameter) =>
    (actualPairResidualInput cutoffScale parameter beta (averagedInactivePair cutoffScale parameter)).kernel word -
    (actualPairReferenceInput cutoffScale parameter beta).kernel word)

/-- The output discrepancy uses the actual target reference, including its
boundary correction, and the complete finite safe-body Neumann input. -/
theorem actualCanonicalPairResidualInput_formula (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (word : Fin 2 → Fin (Parameters.modulus parameter)) :
    (actualCanonicalPairResidualInput cutoffScale parameter beta).kernel word =
      (v7Activation cutoffScale parameter ^ 2)⁻¹ *
        (convolution (actualRootPair parameter).weight
          (actualCompactRootInput parameter 14 (actualPairCoreSeed parameter 14 (averagedInactivePair cutoffScale parameter)))
            (word 0,word 1) -
          SafePair.canonicalPair (actualReferenceLaw cutoffScale parameter beta).weight
            (averagedInactivePair cutoffScale parameter) (word 0) (word 1)) /
        ((actualPrimaryLaw cutoffScale parameter beta).weight (word 0) *
          (actualPrimaryLaw cutoffScale parameter beta).weight (word 1)) := by
  dsimp only [actualCanonicalPairResidualInput, actualPairResidualInput, actualPairReferenceInput, primaryPairSeed, MixedKernel.pairKernel,
    actualPairReferenceChange]
  simp only [Pi.sub_apply, uniformCanonical, LinearMap.coe_mk, AddHom.coe_mk, Fintype.card_fin, one_div]
  ring

/-- The complete literal two-primary residual has the claimed small
activity for the real calibration references and inactive source. -/
theorem actual_canonical_pair_residual_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter) :
    ∀ᶠ parameter in atTop, ∀ (body : FiniteDist (Fin (Parameters.modulus parameter))) (bodyPool radius : ℝ),
      RepresentedPolynomial.inputWeight (actualPrimaryLaw cutoffScale parameter (beta parameter)) body
        (pool parameter : ℝ) bodyPool radius (actualCanonicalPairResidualInput cutoffScale parameter (beta parameter)) ≤
      (Real.sqrt (pool parameter : ℝ))⁻¹ ^ 2 *
        (pairResidualMixedConstant cutoffScale + pairReferenceMixedConstant cutoffScale) / (parameter : ℝ) ^ 2 := by
  filter_upwards [actual_inactive_pair_residual_activity_eventually cutoffScale hscale beta pool htypical,
    actual_pair_reference_activity_eventually cutoffScale hscale beta pool htypical] with parameter hf hr
  intro body bodyPool radius
  rw [actualCanonicalPairResidualInput, primaryPairSeed_weight]
  have hneg (kernel : (Fin 2 → Fin (Parameters.modulus parameter)) → ℝ) :
      MixedKernel.activity ![(Real.sqrt (pool parameter : ℝ))⁻¹,(Real.sqrt (pool parameter : ℝ))⁻¹]
        (MixedKernel.pairReference (actualPrimaryLaw cutoffScale parameter (beta parameter))
          (actualPrimaryLaw cutoffScale parameter (beta parameter))) (-kernel) =
      MixedKernel.activity ![(Real.sqrt (pool parameter : ℝ))⁻¹,(Real.sqrt (pool parameter : ℝ))⁻¹]
        (MixedKernel.pairReference (actualPrimaryLaw cutoffScale parameter (beta parameter))
          (actualPrimaryLaw cutoffScale parameter (beta parameter))) kernel := by
    simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using MixedKernel.activity_smul
      ![(Real.sqrt (pool parameter : ℝ))⁻¹,(Real.sqrt (pool parameter : ℝ))⁻¹]
      (MixedKernel.pairReference (actualPrimaryLaw cutoffScale parameter (beta parameter))
        (actualPrimaryLaw cutoffScale parameter (beta parameter))) kernel (-1)
  let first : (Fin 2 → Fin (Parameters.modulus parameter)) → ℝ :=
    (actualPairResidualInput cutoffScale parameter (beta parameter) (averagedInactivePair cutoffScale parameter)).kernel
  let second : (Fin 2 → Fin (Parameters.modulus parameter)) → ℝ :=
    (actualPairReferenceInput cutoffScale parameter (beta parameter)).kernel
  change MixedKernel.activity _ _ (first - second) ≤ _
  rw [sub_eq_add_neg]
  apply (MixedKernel.activity_add_le _ _ _ _ (fun i => by fin_cases i <;> change 0 ≤ (Real.sqrt (pool parameter : ℝ))⁻¹ <;> positivity)).trans
  rw [hneg]
  have hf' := hf body bodyPool radius
  have hr' := hr body bodyPool radius
  rw [actualPairResidualInput_weight] at hf'
  rw [actualPairReferenceInput, primaryPairSeed_weight] at hr'
  exact (add_le_add hf' hr').trans_eq (by ring)

end
end AFT.V7Calibration

import AFT.JointPairOutput
import AFT.V7PairCompletion

/-! # The literal safe two-body certificate and actual two-primary completion -/

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial SafeConvolution Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The completion's primary seed is already inverted. Its genuine leading
channel is precisely the two-coordinate response occurring in the certificate. -/
theorem actualPairCompletion_seedOutputMass (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hp : ∀ color, (actualPrimaryLaw C n beta).weight color ≠ 0)
    (output : Fin 2 → Fin (Parameters.modulus n)) :
    seedOutputMass (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
      (actualPrimaryChannel C n) (actualBodyChannel n) (actualPairCompletionInput C n beta operator) output =
    v7Activation C n ^ 2 * ((actualPrimaryLaw C n beta).weight (output 0) *
      (actualPrimaryLaw C n beta).weight (output 1)) *
      MixedKernel.inputIteration [1, 0] (fun _ => actualResponse C n)
        (MixedKernel.pairReference (actualPrimaryLaw C n beta) (actualPrimaryLaw C n beta))
        (actualPairCompletionInput C n beta operator).kernel output := by
  have hh := primary_seedOutputMass_iteration (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (v7Activation C n) (actualResponse C n) (actualBodyChannel n)
    (actualPairCompletionInput C n beta operator) rfl hp output
  have hdecision : (fun a b : Fin (Parameters.modulus n) => Classical.propDecidable (a = b)) =
      instDecidableEqFin (Parameters.modulus n) := Subsingleton.elim _ _
  rw [hdecision] at hh
  rw [show primaryCoordinates (actualPairCompletionInput C n beta operator) = [(0 : Fin 2), (1 : Fin 2)] by
    simp [primaryCoordinates, actualPairCompletionInput, primaryPairSeed, List.ofFn_succ]] at hh
  have href : inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
      (actualPairCompletionInput C n beta operator) =
      MixedKernel.pairReference (actualPrimaryLaw C n beta) (actualPrimaryLaw C n beta) := by
    funext slot
    fin_cases slot <;> rfl
  rw [href] at hh
  convert hh using 1
  change _ = v7Activation C n ^ 2 * (∏ slot : Fin 2, (actualPrimaryLaw C n beta).weight (output slot)) * _
  rw [Fin.prod_univ_two]
  rfl

theorem actual_inactive_pair_completed_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ) / (2 * Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2 * (Parameters.legs n : ℝ) / Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → v7Activation C n ≠ 0 →
      (∀ color, (actualPrimaryLaw C n (beta n)).weight color ≠ 0) →
      ∀ output : Fin 2 → Fin (Parameters.modulus n),
      seedOutputMass (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualPrimaryChannel C n) (actualBodyChannel n) (actualInactiveBodyPairInput C n (beta n)) output +
      seedOutputMass (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualPrimaryChannel C n) (actualBodyChannel n) (actualPairCompletionInput C n (beta n) operator) output =
      SafePair.canonicalPair (actualReferenceLaw C n (beta n)).weight (averagedInactivePair C n) (output 0) (output 1) := by
  filter_upwards [actual_inactive_body_pair_outputMass_eventually C hC beta hbeta] with n hb operator hop hrho hp output
  rw [hb, actualPairCompletion_seedOutputMass C n (beta n) operator hp output]
  exact actualPairCompletionInput_exact C n (beta n) operator hop hp hrho output

end
end AFT.V7Calibration

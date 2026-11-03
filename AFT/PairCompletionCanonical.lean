import AFT.V7PairCompletion
import AFT.PrimarySeedCanonical
import AFT.MixedCanonical
import AFT.PrimaryLawLower

/-! # Canonicality of the exact safe-pair primary completion -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

/-- A genuinely zero-marginal signed pair has canonical density under any
strictly positive input law, including a calibrated nonuniform law. -/
theorem pairMassDensity_canonical (primary : FiniteDist Color) (mass : Color × Color → ℝ)
    (hprimary : ∀ color, primary.weight color ≠ 0) (scalar : ℝ)
    (hrow : ∀ first, (∑ second, mass (first,second)) = 0)
    (hcolumn : ∀ second, (∑ first, mass (first,second)) = 0) :
    Hoeffding.Canonical (fun _ : Fin 2 => primary) Finset.univ
      (pairKernel (fun first second => scalar * mass (first,second) / (primary.weight first * primary.weight second))) := by
  apply pair_canonical
  · intro first
    calc
      _ = (scalar / primary.weight first) * ∑ second, mass (first,second) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro second _
        field_simp [hprimary first,hprimary second]
      _ = 0 := by rw [hrow,mul_zero]
  · intro second
    calc
      _ = (scalar / primary.weight second) * ∑ first, mass (first,second) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro first _
        field_simp [hprimary first,hprimary second]
      _ = 0 := by rw [hcolumn,mul_zero]

end
end AFT.MixedKernel

namespace AFT.V7Calibration
open GaussianSource SafeConvolution Filter MixedKernel RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero

theorem actualCanonicalPairResidualInput_canonical (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hcore : (pairCore parameter 14).Nonempty)
    (hprimary : ∀ color, (actualPrimaryLaw cutoffScale parameter beta).weight color ≠ 0) :
    Hoeffding.Canonical (fun _ : Fin 2 => actualPrimaryLaw cutoffScale parameter beta) Finset.univ
      (actualCanonicalPairResidualInput cutoffScale parameter beta).kernel := by
  have hinput := actualCompactRootInput_canonical parameter 14 _
    (actualPairCoreSeed_canonical parameter 14 (averagedInactivePair cutoffScale parameter) hcore)
  have houtput := convolution_pairCanonical (actualRootPair parameter).weight _ hinput
  have htarget : PairCanonical (fun point : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) =>
      SafePair.canonicalPair (actualReferenceLaw cutoffScale parameter beta).weight
        (averagedInactivePair cutoffScale parameter) point.1 point.2) :=
    ⟨SafePair.canonicalPair_first _ _ (actualReferenceLaw cutoffScale parameter beta).sum_one,
      SafePair.canonicalPair_second _ _ (actualReferenceLaw cutoffScale parameter beta).sum_one⟩
  have hdifference := houtput.sub htarget
  have heq : (actualCanonicalPairResidualInput cutoffScale parameter beta).kernel =
      pairKernel (fun first second => (v7Activation cutoffScale parameter ^ 2)⁻¹ *
        (convolution (actualRootPair parameter).weight
          (actualCompactRootInput parameter 14 (actualPairCoreSeed parameter 14 (averagedInactivePair cutoffScale parameter))) (first,second) -
          SafePair.canonicalPair (actualReferenceLaw cutoffScale parameter beta).weight
            (averagedInactivePair cutoffScale parameter) first second) /
        ((actualPrimaryLaw cutoffScale parameter beta).weight first * (actualPrimaryLaw cutoffScale parameter beta).weight second)) := by
    funext word
    exact actualCanonicalPairResidualInput_formula cutoffScale parameter beta word
  rw [heq]
  exact pairMassDensity_canonical _ _ hprimary _ hdifference.1 hdifference.2

/-- The actual finite two-coordinate completion remains canonical after
both inverse operations; the target and root-smoothed safe input both have
exact zero marginals. -/
theorem actual_pair_completion_canonical_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∀ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
      operator.toLinearMap = actualResponse cutoffScale parameter →
      Hoeffding.Canonical (fun _ : Fin 2 => actualPrimaryLaw cutoffScale parameter (beta parameter)) Finset.univ
        (actualPairCompletionInput cutoffScale parameter (beta parameter) operator).kernel := by
  filter_upwards [pairCore_nonempty_eventually 14,
    actual_primary_law_quarter_lower_eventually cutoffScale hscale beta hbeta,
    actualResponse_inverse_mass_eventually cutoffScale hscale] with parameter hcore hp hm operator hop
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hpositive (color : Fin (Parameters.modulus parameter)) :
      (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color ≠ 0 :=
    ne_of_gt ((by positivity : (0 : ℝ) < 1 / (4 * (Parameters.modulus parameter : ℝ))).trans_le (hp color))
  have href : pairReference (actualPrimaryLaw cutoffScale parameter (beta parameter))
      (actualPrimaryLaw cutoffScale parameter (beta parameter)) =
      fun _ : Fin 2 => actualPrimaryLaw cutoffScale parameter (beta parameter) := by
    funext slot
    fin_cases slot <;> rfl
  change Hoeffding.Canonical _ Finset.univ (inputIteration [0,1] (fun _ => operator.symm.toLinearMap)
    (pairReference _ _) (-(actualCanonicalPairResidualInput cutoffScale parameter (beta parameter)).kernel))
  rw [href]
  apply inputIteration_canonical _ _ _ (fun _ _ => hpositive) (fun _ _ => hm operator hop)
  simpa only [neg_one_smul] using canonical_smul _ _ (-1)
    (actualCanonicalPairResidualInput_canonical cutoffScale parameter (beta parameter) hcore hpositive)

end
end AFT.V7Calibration

import AFT.IndependentGlobalImage
import AFT.IndependentUpperInverse

/-! # Exact truncated physical image of the literal independent upper operator -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentUpperImageFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem actualLeadingOutput_truncate (C : ℝ) (n : ℕ) (beta : ℝ) (cutoff : ℕ)
    (table : Table (InputSeed (Fin (Parameters.modulus n)))) :
    truncate (fun _ => 1) cutoff (actualLeadingOutput C n beta
      (truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff table))=
      truncate (fun _ => 1) cutoff (actualLeadingOutput C n beta table) :=
  outputHom_truncation_respects _ _ _ _ cutoff _ _ (truncate_idempotent _ _ _)

theorem independentUpperLinear_monomial_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (cutoff depth : ℕ) (powers : InputSeed (Fin (Parameters.modulus n)) →₀ ℕ)
    (horder : weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers ≤ cutoff)
    (hcanonical : ∀ seed ∈ powers.support,Hoeffding.Canonical
      (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) seed) Finset.univ seed.kernel) :
    truncate (fun _ => 1) cutoff (actualLeadingOutput C n beta
      ((1+independentUpperLinear C n beta operator charts cutoff depth) (MvPolynomial.monomial powers 1)))=
    truncate (fun _ => 1) cutoff (actualLeadingOutput C n beta
      (independentGlobalQuotient C n beta operator charts (mixedMonomialSeed powers) depth)) := by
  simp only [LinearMap.add_apply,Module.End.one_apply,
    independentUpperLinear_monomial C n beta operator charts cutoff depth powers 1 horder hcanonical,one_smul]
  rw [map_add,truncate_add,actualLeadingOutput_truncate,map_sub,truncate_sub]
  have hm : actualLeadingOutput C n beta (MvPolynomial.X (mixedMonomialSeed powers))=
      actualLeadingOutput C n beta (MvPolynomial.monomial powers 1) := by
    rw [actualLeadingOutput,outputHom_X,mixedMonomialSeed_output]
  rw [hm]
  ring

/-- The bounded literal operator has the full joint physical quotient image,
not merely its first-degree response or an assumed substitution homomorphism. -/
theorem independentUpperLinear_physical_image_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ cutoff depth : ℕ,∀ powers : InputSeed (Fin (Parameters.modulus n)) →₀ ℕ,
    weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers ≤ cutoff →
    (∀ seed ∈ powers.support,Hoeffding.Canonical
      (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed) Finset.univ seed.kernel) →
    truncate (fun _ => 1) cutoff (actualLeadingOutput C n (beta n)
      ((1+independentUpperLinear C n (beta n) operator charts cutoff depth) (MvPolynomial.monomial powers 1)))=
    truncate (fun _ => 1) cutoff
      (pendingPhysicalPolynomial C n (beta n) charts (initialPendingInput (mixedMonomialSeed powers))*
        (finiteCorrection (centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
          (independentPairedPositiveMass C n (beta n) charts)-1) depth)^(mixedMonomialSeed powers).primaryOrder*
        (finiteCorrection (centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
          (independentBodyPositiveMass C n (beta n))-1) depth)^(mixedMonomialSeed powers).bodyOrder) := by
  filter_upwards [independentGlobalQuotient_image_eventually C hC beta hbeta]
    with n hi operator hop charts hc cutoff depth powers ho hs
  rw [independentUpperLinear_monomial_image C n (beta n) operator charts cutoff depth powers ho hs,
    hi operator hop charts hc (mixedMonomialSeed powers) (mixedMonomialSeed_canonical _ _ powers hs) depth]

end
end AFT.V7Calibration

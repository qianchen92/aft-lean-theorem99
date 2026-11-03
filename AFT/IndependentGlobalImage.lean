import AFT.PendingPhysicalIdentity
import AFT.IndependentGlobalQuotient

/-! # The literal joint independent quotient has its complete physical image -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentGlobalImageFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem independentPositiveReciprocal_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,0 < (actualPrimaryLaw C n beta).weight color)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (hmass : ∑ word,independentPairedPositiveMass C n beta charts word=1) (depth : ℕ) :
    actualLeadingOutput C n beta (independentPositiveReciprocal C n beta operator charts depth)=
      finiteCorrection (centeredGeneratingLinear (actualReferenceLaw C n beta).weight
        (independentPairedPositiveMass C n beta charts)-1) depth := by
  have hd := actual_referenceCoefficientTable_inverse_image C n beta operator hop hrho hp
    (independentPairedPositiveMass C n beta charts)
  rw [hmass,map_one] at hd
  simp only [independentPositiveReciprocal,independentPositiveInputTable,referenceInverseTable,finiteCorrection,
    map_sum,map_pow,map_neg,hd]

/-- All original primary channels are replaced jointly; every original body
channel is retained, and the two factors are the actual positive block laws. -/
theorem independentGlobalQuotient_image_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel → ∀ depth : ℕ,
    actualLeadingOutput C n (beta n) (independentGlobalQuotient C n (beta n) operator charts seed depth)=
      pendingPhysicalPolynomial C n (beta n) charts (initialPendingInput seed)*
        (finiteCorrection (centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
          (independentPairedPositiveMass C n (beta n) charts)-1) depth)^seed.primaryOrder*
        (finiteCorrection (centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
          (independentBodyPositiveMass C n (beta n))-1) depth)^seed.bodyOrder := by
  filter_upwards [independentNumeratorTable_image_eventually C hC beta hbeta,
    independentPairedPositiveMass_probability_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,actual_primary_probability_eventually C hC beta hbeta,
    eventually_ge_atTop 2] with n hi hm hl hp hn operator hop charts hc seed hs depth
  have hp0 (color) : 0 < (actualPrimaryLaw C n (beta n)).weight color := by rw [hl.1]; exact hp.1 color
  have hrho : v7Activation C n ≠ 0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).ne'
  simp only [independentGlobalQuotient,map_mul,map_pow,hi operator hop charts hc seed hs,
    independentPositiveReciprocal_image C n (beta n) operator hop hrho hp0 charts (hm charts).2,
    independentBodyReciprocal_image C n (beta n) operator hop hrho hp0]

end
end AFT.V7Calibration

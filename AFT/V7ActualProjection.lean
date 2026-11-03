import AFT.V7ActualPrimary
import AFT.V7SafeProjection

/-! # Actual-source boundary projection for the calibrated inverse -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem actual_anchor_margin_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop,
      (∀ sample : pairSample cutoffScale parameter,
        (Parameters.safeMargin parameter : ℤ) + |bodyShift cutoffScale parameter sample.1| ≤ Parameters.anchorWidth parameter) ∧
      (∀ sample : pairSample cutoffScale parameter,
        (Parameters.safeMargin parameter : ℤ) + |compensatorRootShift cutoffScale parameter sample| ≤ Parameters.anchorWidth parameter) := by
  filter_upwards [legCutoff_le_square_eventually cutoffScale hscale, eventually_ge_atTop 2] with parameter hl hp
  have hmax : maxBodyShift cutoffScale parameter ≤ 5 * parameter ^ 2 := by
    unfold maxBodyShift v7RootCutoff queueCutoff
    omega
  have hpower : 25 * parameter ^ 2 ≤ Parameters.anchorWidth parameter := by
    have hh : 25 ≤ parameter ^ 30 := by have hh := Nat.pow_le_pow_left hp 30; omega
    have hh' := Nat.mul_le_mul_right (parameter ^ 2) hh
    simpa only [Parameters.anchorWidth, Parameters.security_eq parameter hp, ← pow_add] using hh'
  have hmargin : Parameters.safeMargin parameter = 20 * parameter ^ 2 := by
    simp only [Parameters.safeMargin, Parameters.security_eq parameter hp]
  constructor
  · intro sample
    have hh := bodyShift_abs_le cutoffScale parameter sample.1
    omega
  · intro sample
    have hh := Finset.mem_Icc.mp sample.1.1.property
    dsimp only [compensatorRootShift]
    have hh' := abs_le.mpr hh
    unfold v7RootCutoff at hh'
    omega

/-- The actual inverse conjugates the boundary ideal projection to a legal
input projection; all anchor and source requirements are discharged. -/
theorem actual_safe_projection_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (htypical : ∀ᶠ parameter : ℕ in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter : ℕ in atTop,
      let interior := (boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter))ᶜ
      ∀ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = actualResponse cutoffScale parameter →
        (∀ profile, legalInputProjection operator (boundaryIdealProjection interior (actualPrimary cutoffScale (beta parameter) parameter)) profile ∈
          canonicalInteriorProfiles interior) ∧
        (∀ profile, operator (legalInputProjection operator (boundaryIdealProjection interior (actualPrimary cutoffScale (beta parameter) parameter)) profile) =
          boundaryIdealProjection interior (actualPrimary cutoffScale (beta parameter) parameter) (operator profile)) ∧
        (∀ profile ∈ canonicalInteriorProfiles interior,
          legalInputProjection operator (boundaryIdealProjection interior (actualPrimary cutoffScale (beta parameter) parameter)) profile = profile) := by
  have hmodel := actual_physical_supports_eventually cutoffScale hscale
  have hp := V7Calibration.primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) (by
      filter_upwards [hmodel, htypical] with parameter hs ht
      exact ⟨hs.1, hs.2, ht⟩)
  filter_upwards [hmodel, hp, actual_anchor_margin_eventually cutoffScale hscale] with parameter hs hp hm
  dsimp only
  intro operator hop
  apply V7Calibration.response_safe_projection parameter cutoffScale (boundaryHalf cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter) (pairSourceShift cutoffScale parameter)
    (pairSourceLaw cutoffScale parameter) (fun sample => bodyShift cutoffScale parameter sample.1)
    (compensatorRootShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter)
    (actualPrimary cutoffScale (beta parameter) parameter) hs.1.1.1 hs.1.1.2
  · have hh := Parameters.safeSize_positive parameter
    unfold Parameters.safeSize at hh
    have hboundary := hs.1.1.2
    omega
  · exact hm.1
  · exact hm.2
  · intro color
    exact lt_of_lt_of_le (by have hh := (Parameters.modulus_prime parameter).pos; positivity) (hp.1 color)
  · exact hp.2.2.2.1
  · exact hop

end
end AFT.GaussianSource

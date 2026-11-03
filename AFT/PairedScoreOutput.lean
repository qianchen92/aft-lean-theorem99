import AFT.ActualWeightedTriples
import AFT.RootCompensator

/-! # Literal paired scores applied to the physical chart and compensator -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

/-- Exact product response of a paired score. The compensating reference
may vanish outside its actual support. -/
theorem pairedLift_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (primary : ι → ℝ) (body : κ → ℝ) (anchor : ι → κ → ℝ)
    (activation : ℝ) (profile first : ι → ℝ) (second : κ → ℝ)
    (hp : ∀ color, primary color ≠ 0)
    (hbody : ∀ center, body center = 0 → applyAnchor anchor profile center = 0) :
    (∑ color, ∑ center, primary color * body center *
      pairedLift primary body anchor activation profile color center *
        first color * second center) =
      (∑ color, profile color * first color) * (∑ center, body center * second center) -
        activation * (∑ color, primary color * first color) *
          (∑ center, applyAnchor anchor profile center * second center) := by
  have hpoint (color : ι) (center : κ) :
      primary color * body center * pairedLift primary body anchor activation profile color center *
        first color * second center =
      (profile color * first color) * (body center * second center) -
        (activation * primary color * first color) * (applyAnchor anchor profile center * second center) := by
    by_cases hb : body center = 0
    · simp only [hb, hbody center hb, mul_zero, zero_mul, sub_zero]
    · unfold pairedLift
      field_simp [hp color, hb]
  have hfactor : (∑ color, activation * primary color * first color) =
      activation * ∑ color, primary color * first color := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro color _
    ring
  simp only [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hfactor]

/-- Additive-count response on the genuine safe support. -/
theorem pairedLift_firstMoment_supported {ι κ : Type*} [Fintype ι] [Fintype κ]
    (primary : ι → ℝ) (body : κ → ℝ) (anchor : ι → κ → ℝ)
    (activation : ℝ) (profile first : ι → ℝ) (second : κ → ℝ)
    (hp : ∀ color, primary color ≠ 0)
    (hbody : ∀ center, body center = 0 → applyAnchor anchor profile center = 0)
    (hpmass : ∑ color, primary color = 1) (hbmass : ∑ center, body center = 1)
    (hamass : ∀ color, ∑ center, anchor color center = 1)
    (hcanonical : ∑ color, profile color = 0) :
    (∑ color, ∑ center, primary color * body center *
      pairedLift primary body anchor activation profile color center * (first color + second center)) =
      (∑ color, profile color * first color) -
        activation * ∑ center, applyAnchor anchor profile center * second center := by
  have h := independentScore_firstMoment primary body
    (fun color => profile color / primary color) first
    (fun center => applyAnchor anchor profile center / body center) second activation
  have hpCancel (color) : primary color * (profile color / primary color) = profile color := by
    field_simp [hp color]
  have hbCancel (center) : body center * (applyAnchor anchor profile center / body center) =
      applyAnchor anchor profile center := by
    by_cases hb : body center = 0
    · simp only [hb, hbody center hb, zero_div, mul_zero]
    · field_simp
  simp only [hpCancel, hbCancel, hpmass, hbmass, applyAnchor_mass anchor profile hamass,
    hcanonical, mul_zero, zero_mul, mul_one, add_zero, sub_zero] at h
  simpa only [pairedLift, mul_div_assoc] using h

namespace V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance pairedScoreFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Actual safe compensation vanishes wherever the actual body probability
vanishes; no positivity assumption is imposed on impossible centers. -/
theorem actual_anchor_supported_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ,
      ∀ center, (actualBodyLaw cutoffScale parameter (beta parameter)).weight center = 0 →
        applyAnchor (fun color output => publicAnchorKernel (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color output.val) profile center = 0 := by
  filter_upwards [actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta] with parameter hl hb
  intro profile center hc
  have hout : center ∉ safePalette parameter := by
    intro hin
    have hcore : 0 < (actualCoreLaw parameter).weight center := by
      rw [actualCoreLaw_weight]
      simp only [uniformFiniteProfile, if_pos hin]
      have hcard : 0 < (safePalette parameter).card := Finset.card_pos.mpr (safePalette_nonempty parameter)
      positivity
    rw [hl.2.1] at hc
    linarith [(hb.2.1 center).1]
  unfold applyAnchor
  apply Finset.sum_eq_zero
  intro color _
  dsimp only
  rw [(actual_anchor_safe_mass parameter color).2 center hout, zero_mul]

/-- The true signed four-output numerator: actual primary, safe compensator,
positive affine charts, Gaussian sources, body blur and the root-only
compensator channel all occur with their original finite probabilities. -/
def actualPairedChartRaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (profile : Fin (Parameters.modulus parameter) → ℝ)
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ)
    (first second output : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ mark, ∑ center,
    (actualPrimaryLaw cutoffScale parameter beta).weight mark *
      (actualBodyLaw cutoffScale parameter beta).weight center *
      pairedLift (actualPrimaryLaw cutoffScale parameter beta).weight
        (actualBodyLaw cutoffScale parameter beta).weight
        (fun color position => publicAnchorKernel (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color position.val)
        (v7Activation cutoffScale parameter) profile mark center *
      publicChartRaw cutoffScale parameter mark (charts mark) attached first second *
      rootCompensatorChannel parameter center output

/-- The paired numerator is derived from the actual chart construction,
including the negative compensator contribution and source-dependent attachment. -/
theorem actual_paired_score_chart_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ mark, profile mark) = 0 →
      ∀ (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ)
        (first second output : Fin (Parameters.modulus parameter)),
        actualPairedChartRaw cutoffScale parameter (beta parameter) charts profile attached first second output =
          primaryJointNumerator cutoffScale parameter profile attached first second *
            (∑ center, (actualBodyLaw cutoffScale parameter (beta parameter)).weight center * rootCompensatorChannel parameter center output) -
          v7Activation cutoffScale parameter *
            (∑ mark, (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark *
              publicChartRaw cutoffScale parameter mark (charts mark) attached first second) *
            (∑ center, applyAnchor (fun color position => publicAnchorKernel (Parameters.modulus parameter)
              (Parameters.anchorWidth parameter) color position.val) profile center * rootCompensatorChannel parameter center output) := by
  filter_upwards [public_chart_joint_output_eventually cutoffScale hscale,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_anchor_supported_eventually cutoffScale hscale beta hbeta] with parameter hc hl hp hs
  choose charts hcharts using hc
  refine ⟨charts, ?_⟩
  intro profile hcanonical attached first second output
  unfold actualPairedChartRaw
  rw [pairedLift_product _ _ _ _ _ _ _ (fun color => by rw [hl.1]; exact (hp.1 color).ne') (hs profile)]
  have hh : (∑ mark, profile mark * publicChartRaw cutoffScale parameter mark (charts mark) attached first second) =
      primaryJointNumerator cutoffScale parameter profile attached first second := by
    simp only [hcharts]
    exact conditionalJointOutput_signed cutoffScale parameter profile hcanonical attached first second
  rw [hh]

end V7Calibration
end
end AFT

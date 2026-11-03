import AFT.FixedChartMarginals
import AFT.FixedPairedFirst
import AFT.FourOutputCounts
import AFT.FourOutputCountInstances

/-! # Actual four-output cancellation and first count before root averaging -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration PhysicalBlockTensors Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance fixedMomentsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def publicAnchorFiniteProfile (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) : Fin (Parameters.modulus parameter) → ℝ :=
  applyAnchor (fun color position => publicAnchorKernel (Parameters.modulus parameter)
    (Parameters.anchorWidth parameter) color position.val) profile

theorem publicAnchorFiniteProfile_safe (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (center : Fin (Parameters.modulus parameter))
    (hout : center ∉ safePalette parameter) : publicAnchorFiniteProfile parameter profile center = 0 := by
  unfold publicAnchorFiniteProfile applyAnchor
  apply Finset.sum_eq_zero
  intro color _
  change publicAnchorKernel _ _ color center.val * profile color = 0
  rw [(actual_anchor_safe_mass parameter color).2 center hout, zero_mul]

theorem publicAnchorFiniteProfile_mass (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) :
    (∑ center, publicAnchorFiniteProfile parameter profile center) = ∑ color, profile color :=
  applyAnchor_mass _ _ (fun color => (actual_anchor_safe_mass parameter color).1)

theorem shifted_publicAnchorFiniteProfile (parameter : ℕ) (root : ℤ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    integerShiftProfile parameter (publicAnchorFiniteProfile parameter profile) root output =
      integerAnchorShiftProfile parameter root profile output := by
  have hh := singleRoot_anchorProfile parameter root profile output
  simpa only [publicAnchorFiniteProfile, integerShiftProfile, mul_ite, mul_one, mul_zero] using hh

/-- The score is expanded only after the genuine four-output sampling law
has been fixed. Its negative term retains the original unweighted triple. -/
theorem fixedPairedChartRaw_factor_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    ∀ attachedRoot compensatorRoot queue : ℤ, ∀ profile : Fin (Parameters.modulus parameter) → ℝ,
    ∀ word : Fin 4 → Fin (Parameters.modulus parameter),
      fixedPairedChartRaw cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile word =
        signedChartTriple cutoffScale parameter (beta parameter) charts attachedRoot queue profile (word 0) (word 1) (word 2) *
          integerShiftProfile parameter (actualBodyLaw cutoffScale parameter (beta parameter)).weight compensatorRoot (word 3) -
        v7Activation cutoffScale parameter *
          (signedChartTriple cutoffScale parameter (beta parameter) charts attachedRoot queue
            (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word 0) (word 1) (word 2) *
          integerShiftProfile parameter (publicAnchorFiniteProfile parameter profile) compensatorRoot (word 3)) := by
  filter_upwards [actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_anchor_supported_eventually cutoffScale hscale beta hbeta] with parameter hl hp hs charts ar cr queue profile word
  unfold fixedPairedChartRaw
  rw [pairedLift_product _ _ _ _ _ _ _ (fun color => by rw [hl.1]; exact (hp.1 color).ne') (hs profile)]
  simp only [signedChartTriple, fixedChartTriple, integerShiftProfile, publicAnchorFiniteProfile,
    mul_ite, mul_one, mul_zero]
  ring

/-- Both signed-profile masses are preserved by their literal integer
root translation because their true supports lie in the safe interval. -/
theorem fixed_compensator_masses_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root : ℤ, |root| ≤ (v7RootCutoff parameter : ℤ) →
      (∑ output, integerShiftProfile parameter (actualBodyLaw cutoffScale parameter (beta parameter)).weight root output) = 1 ∧
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ,
        (∑ output, integerShiftProfile parameter (publicAnchorFiniteProfile parameter profile) root output) = ∑ color, profile color := by
  filter_upwards [body_support_scales_eventually cutoffScale hscale,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta] with parameter hs hb hl root hr
  have hm : |root| ≤ (Parameters.safeMargin parameter : ℤ) := by
    have hh : v7RootCutoff parameter ≤ maxBodyShift cutoffScale parameter := by unfold maxBodyShift; omega
    exact hr.trans (by exact_mod_cast hh.trans hs.1)
  constructor
  · rw [integerShiftProfile_mass parameter _ (fun color hout => by rw [hl.2.1]; exact hb.2.2 color hout) root hm]
    exact (actualBodyLaw cutoffScale parameter (beta parameter)).sum_one
  · intro profile
    rw [integerShiftProfile_mass parameter _ (publicAnchorFiniteProfile_safe parameter profile) root hm,
      publicAnchorFiniteProfile_mass]

/-- The complete literal four-output signed block has total mass zero for
every realized legal compensator root and every chart selection. -/
theorem fixedPairedChartRaw_mass_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    ∀ attachedRoot compensatorRoot queue : ℤ, |compensatorRoot| ≤ (v7RootCutoff parameter : ℤ) →
    ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ color, profile color) = 0 →
      (∑ word, fixedPairedChartRaw cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile word) = 0 := by
  filter_upwards [fixedPairedChartRaw_factor_eventually cutoffScale hscale beta hbeta,
    fixed_compensator_masses_eventually cutoffScale hscale beta hbeta] with parameter hf hm charts ar cr queue hcr profile hp
  let first := signedChartTriple cutoffScale parameter (beta parameter) charts ar queue profile
  let second := signedChartTriple cutoffScale parameter (beta parameter) charts ar queue
    (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight
  let body := integerShiftProfile parameter (actualBodyLaw cutoffScale parameter (beta parameter)).weight cr
  let anchor := integerShiftProfile parameter (publicAnchorFiniteProfile parameter profile) cr
  have hmass1 := four_output_product_mass_instance first body
  have hmass2 := four_output_product_mass_instance second anchor
  have ht1 : (∑ a, ∑ b, ∑ c, first a b c) = 0 := (signedChartTriple_total _ _ _ _ _ _ _).trans hp
  have ht2 : (∑ a, ∑ b, ∑ c, second a b c) = 1 :=
    (signedChartTriple_total _ _ _ _ _ _ _).trans (actualPrimaryLaw cutoffScale parameter (beta parameter)).sum_one
  have hc1 : (∑ output, body output) = 1 := (hm cr hcr).1
  have hc2 : (∑ output, anchor output) = 0 := ((hm cr hcr).2 profile).trans hp
  calc
    _ = (∑ word : Fin 4 → Fin (Parameters.modulus parameter), first (word 0) (word 1) (word 2) * body (word 3)) -
        v7Activation cutoffScale parameter * ∑ word : Fin 4 → Fin (Parameters.modulus parameter),
          second (word 0) (word 1) (word 2) * anchor (word 3) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun word _ => hf charts ar cr queue profile word)
    _ = 0 := by rw [hmass1, hmass2, ht1, ht2, hc1, hc2]; ring

/-- The complete four-output count equals the actual endpoint-plus-root
compensator expression. The attached body cancels exactly. -/
theorem fixedPairedChartRaw_count_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    ∀ attachedRoot compensatorRoot queue : ℤ, |compensatorRoot| ≤ (v7RootCutoff parameter : ℤ) →
    ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ color, profile color) = 0 →
    ∀ output, fourOutputCount (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile) output =
      fixedPairedFirstCount cutoffScale parameter (beta parameter) charts compensatorRoot profile output := by
  filter_upwards [fixedPairedChartRaw_factor_eventually cutoffScale hscale beta hbeta,
    fixed_compensator_masses_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_anchor_supported_eventually cutoffScale hscale beta hbeta]
    with parameter hf hm hl hp hs charts ar cr queue hcr profile hcanonical output
  have hcount : fourOutputCount (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts ar cr queue profile) output =
      fourOutputCount (fun word => signedChartTriple cutoffScale parameter (beta parameter) charts ar queue profile (word 0) (word 1) (word 2) *
        integerShiftProfile parameter (actualBodyLaw cutoffScale parameter (beta parameter)).weight cr (word 3)) output -
      v7Activation cutoffScale parameter * fourOutputCount (fun word => signedChartTriple cutoffScale parameter (beta parameter) charts ar queue
        (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word 0) (word 1) (word 2) *
        integerShiftProfile parameter (publicAnchorFiniteProfile parameter profile) cr (word 3)) output := by
    simp only [fourOutputCount, hf charts ar cr queue profile, sub_mul, mul_assoc,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hcount, four_output_product_count, four_output_product_count,
    signedChartTriple_total, signedChartTriple_total, (hm cr hcr).1,
    (hm cr hcr).2 profile, hcanonical, (actualPrimaryLaw cutoffScale parameter (beta parameter)).sum_one]
  simp only [mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
  change tripleOutputCount (signedChartTriple cutoffScale parameter (beta parameter) charts ar queue profile) output - _ = _
  rw [show tripleOutputCount (signedChartTriple cutoffScale parameter (beta parameter) charts ar queue profile) output =
      ∑ mark, profile mark * publicChartEndpointMean cutoffScale parameter mark (charts mark) output from
    signedChartTriple_count _ _ _ _ _ _ _ hcanonical output]
  unfold fixedPairedFirstCount
  rw [pairedLift_firstMoment_supported _ _ _ _ _ _ _
    (fun color => by rw [hl.1]; exact (hp.1 color).ne') (hs profile)
    (actualPrimaryLaw cutoffScale parameter (beta parameter)).sum_one
    (actualBodyLaw cutoffScale parameter (beta parameter)).sum_one
    (fun color => (actual_anchor_safe_mass parameter color).1) hcanonical]
  simp only [integerShiftProfile, publicAnchorFiniteProfile, mul_ite, mul_one, mul_zero]

end
end AFT.V7Calibration

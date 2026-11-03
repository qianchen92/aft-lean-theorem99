import AFT.IndependentPositiveFibers
import AFT.ReferenceSingletonComponent
import AFT.SharpReferenceActivity
import AFT.ReferencePrimaryDensity
import AFT.PrimaryLawLower

/-! # Sharp reference-centered literal activities of the independent-root paired coefficients -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPositiveActivityFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPositiveActivitySubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Every actual homogeneous coefficient has a literal input activity at
most lambda^4 times its correctly normalized old primary activity. This
uses the original joint root law only through independent marginal copies. -/
theorem independentPairedPositive_component_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ (selected : Finset (Fin 4)) (rate : ℝ), 0 ≤ rate → rate ≤ 1 → rate * (parameter : ℝ) ^ 4 ≤ 1 →
    MixedKernel.activity (fun _ : selected => rate)
      (fun _ : selected => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
        (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter))
        (independentPairedPositiveMass cutoffScale parameter (beta parameter) charts) selected) ≤
      (2*2097152*100000000) * rate ^ selected.card * (parameter : ℝ) ^ 4 := by
  filter_upwards [independentPairedPositiveDensity_fibers_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_primary_density_eventually cutoffScale hscale beta hbeta]
    with parameter h hl hp hcompare charts hc selected rate hrate hrate1 hsmall
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let full : ℝ := 100000000 * (parameter : ℝ)^4
  let single := full
  have hh := h charts hc
  have hfull : 0 ≤ full := by positivity
  have hsingle : 0 ≤ single := by positivity
  have hF : (FiniteDist.independent (fun _ : Fin 4 => primary)).l2Sq
      (independentPairedPositiveDensity cutoffScale parameter (beta parameter) charts) ≤ full^2 := by
    have heq : full ^ 2 = (100000000 : ℝ)^2 * (parameter : ℝ)^8 := by
      dsimp [full]
      rw [mul_pow]
      ring
    rw [heq]
    exact hh.1.trans (by gcongr; norm_num)
  have hG (slot : Fin 4) (values) :
      MixedKernel.fiberSq (fun _ : Fin 4 => primary)
        (independentPairedPositiveDensity cutoffScale parameter (beta parameter) charts) {slot} values ≤ single^2 := by
    have heq : single ^ 2 = (100000000 : ℝ)^2 * (parameter : ℝ)^8 := by dsimp [single,full]; ring
    rw [heq]
    exact (hh.2.1 slot values).trans (by gcongr; norm_num)
  have hH (word) : |independentPairedPositiveDensity cutoffScale parameter (beta parameter) charts word| ≤
      (parameter : ℝ)^4 * single := by
    apply (hh.2.2 word).trans
    have heq : (parameter : ℝ)^4 * single = 100000000 * (parameter : ℝ)^8 := by dsimp [single,full]; ring
    rw [heq]
    gcongr
    norm_num
  have href (slot : Fin 4) (color) : 0 < primary.weight color := by
    change 0 < (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color
    rw [hl.1]
    exact hp.1 color
  have hcomparison (slot : Fin 4) (color) :
      (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color ≤ 8 * primary.weight color := by
    have hc := (hcompare.1 color)
    have hpp : 0 < actualPrimary cutoffScale parameter (beta parameter) color := hp.1 color
    have hh := (le_abs_self _).trans hc
    have hout := (div_le_iff₀ hpp).mp hh
    simpa only [primary, hl.1, hl.2.2] using hout
  have hc4 : selected.card ≤ 4 := by simpa only [Fintype.card_fin] using Finset.card_le_univ selected
  have hout := LocalTensors.referenceRestrictedComponent_activity_sharp (fun _ : Fin 4 => primary)
    (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter)) href hcomparison (independentPairedPositiveMass cutoffScale parameter (beta parameter) charts) selected hc4
    rate full single ((parameter : ℝ)^4) hrate hrate1 hfull hsingle (by positivity) hsmall hF hG hH
  apply hout.trans
  have hbr : full + rate*single ≤ 2*full := by
    have hh := mul_le_mul_of_nonneg_right hrate1 hfull
    dsimp [single] at *
    linarith
  have hh := mul_le_mul_of_nonneg_left hbr
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2097152) (pow_nonneg hrate selected.card))
  exact hh.trans_eq (by dsimp [full]; ring)


/-- The genuine positive denominator's linear coefficients cost only a
constant times the new primary-coordinate rate. -/
theorem independentPairedPositive_linear_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second,publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ (selected : Finset (Fin 4)), selected.card=1 → ∀ rate : ℝ, 0 ≤ rate → rate ≤ 1 →
    MixedKernel.activity (fun _ : selected => rate)
      (fun _ : selected => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (LocalTensors.referenceRestrictedComponent
        (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
        (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter))
        (independentPairedPositiveMass cutoffScale parameter (beta parameter) charts) selected) ≤ 4112*rate := by
  filter_upwards [independentPairedPositiveMass_bounds_eventually cutoffScale hscale beta hbeta,
    independentPairedPositiveMass_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_primary_density_eventually cutoffScale hscale beta hbeta]
    with parameter hb hm hl hp hr charts hc selected hselected rate hrate hrate1
  have hp0 (color) : 0 < (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.1]
    exact hp.1 color
  have hcomparison (slot : Fin 4) (color) :
      (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color ≤
        8*(actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color := by
    have hh := (div_le_iff₀ (hp.1 color)).mp ((le_abs_self _).trans (hr.1 color))
    simpa only [hl.1,hl.2.2] using hh
  have hh := LocalTensors.referenceRestrictedComponent_linear_activity_le
    (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
    (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter)) (fun _ => hp0)
    (independentPairedPositiveMass cutoffScale parameter (beta parameter) charts)
    (hm charts).1 (hm charts).2 8 2048 rate (by norm_num) (by norm_num) hrate hrate1
    hcomparison (hb charts hc).2 selected hselected
  exact hh.trans_eq (by ring)

end
end AFT.V7Calibration

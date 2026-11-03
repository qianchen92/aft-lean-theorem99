import AFT.BackgroundReference

/-! # Explicit body/reference norm bounds for the actual calibrated model -/

namespace AFT.V7Calibration

open Filter
open scoped BigOperators Classical Topology

noncomputable section

def bodyMean {σ : Type*} [Fintype σ] (parameter : ℕ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ) : Fin (Parameters.modulus parameter) → ℝ :=
  fun color => TrimmedSlice.blurredSafeLaw (Parameters.modulus parameter) (Parameters.safeMargin parameter)
    bodyShifts bodyLaw.weight color.val

def bodyCompensation (parameter : ℕ) (cutoffScale : ℝ) : ℝ :=
  (Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter / Parameters.bodies parameter

/-- Every premise is a physical support or typical-beta condition. The
weighted norm and relative density estimates are outputs of the actual
calibration, with the boundary L1 gain explicitly retained. -/
theorem body_reference_bounds_eventually {σ τ : ℕ → Type*}
    [∀ parameter, Fintype (σ parameter)] [∀ parameter, Fintype (τ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ) (boundary : ℕ → ℤ)
    (bodyShifts : (parameter : ℕ) → σ parameter → ℤ)
    (bodyLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (startsPlus startsMinus sources : (parameter : ℕ) → τ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (τ parameter))
    (hmodel : ∀ᶠ parameter in atTop,
      PhysicalSupports parameter cutoffScale (boundary parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter) ∧
      (∀ index, |bodyShifts parameter index| ≤ (Parameters.safeMargin parameter : ℤ) - boundary parameter) ∧
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      let p := primary parameter cutoffScale (beta parameter) (boundary parameter)
        (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
        (sources parameter) (sourceLaw parameter)
      let B := bodyMean parameter (bodyShifts parameter) (bodyLaw parameter)
      let r := referenceMean parameter cutoffScale (beta parameter) (boundary parameter)
      let relative := 5 * bodyCompensation parameter cutoffScale +
        8 * (Parameters.safeMargin parameter : ℝ) /
          ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter)
      (∀ color, |B color - r color| ≤ relative * p color) ∧
      profileSquareNorm p (B - r) ≤ relative *
        (8 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter) := by
  have hphysical := hmodel.mono fun _ h => h.1
  filter_upwards [hmodel, body_deficit_eventually cutoffScale hscale beta boundary bodyShifts bodyLaw
    startsPlus startsMinus sources sourceLaw hmodel,
    primary_estimates_eventually cutoffScale hscale beta boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw hmodel,
    primary_ge_half_base_eventually cutoffScale hscale beta boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw hmodel,
    base_sign_estimates_eventually cutoffScale hscale boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw hphysical,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary (hphysical.mono fun _ h => h.1),
    eventually_ge_atTop 1] with parameter hm hdef hp hhalf hbase hclear hlarge
  dsimp only
  let p := primary parameter cutoffScale (beta parameter) (boundary parameter)
    (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
    (sources parameter) (sourceLaw parameter)
  let B := bodyMean parameter (bodyShifts parameter) (bodyLaw parameter)
  let r := referenceMean parameter cutoffScale (beta parameter) (boundary parameter)
  let base := basePrimary parameter cutoffScale (boundary parameter)
    (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
    (sources parameter) (sourceLaw parameter)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hN : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  have hpop : (Parameters.bodies parameter : ℝ) ≤ Parameters.dimension parameter := by
    exact_mod_cast (show Parameters.bodies parameter ≤ Parameters.dimension parameter by
      have hh := Parameters.population_identity parameter; omega)
  have hn : (0 : ℝ) < Parameters.dimension parameter := hN.trans_le hpop
  have ha : 0 < GaussianSource.v7Activation cutoffScale parameter :=
    GaussianSource.activation_positive _ _ _ _ (GaussianSource.legFeatureCount_positive cutoffScale parameter hscale hlarge)
  have hm0 : (0 : ℝ) ≤ Parameters.legs parameter := Nat.cast_nonneg _
  have hmargin0 : (0 : ℝ) ≤ Parameters.safeMargin parameter := Nat.cast_nonneg _
  have hsmall : 4 * (Parameters.safeMargin parameter : ℝ) ≤ Parameters.modulus parameter := by exact_mod_cast hclear.1
  have hsafe : 0 < (Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter := by linarith
  have hsafeInt : 2 * (Parameters.safeMargin parameter : ℤ) < Parameters.modulus parameter := by exact_mod_cast (sub_pos.mp hsafe)
  have hshifts : ∀ i, |bodyShifts parameter i| ≤ (Parameters.safeMargin parameter : ℤ) := by
    intro i
    have hh := hm.2.1 i
    have hb := hm.1.1.1
    omega
  have hp0 (color) : 0 < p color := lt_of_lt_of_le (by positivity) (hp.1 color)
  have hbody0 (color) : 0 ≤ B color := by
    dsimp only [B, bodyMean, TrimmedSlice.blurredSafeLaw]
    exact Finset.sum_nonneg fun i _ => mul_nonneg ((bodyLaw parameter).nonneg i) (intervalAnchorLaw_nonneg _ _ _)
  have hbodyUpper (color) : B color ≤ 1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) := by
    exact_mod_cast TrimmedSlice.blurredSafeLaw_le (Parameters.modulus parameter) (Parameters.safeMargin parameter)
      (bodyShifts parameter) (bodyLaw parameter).weight (bodyLaw parameter).nonneg (bodyLaw parameter).sum_one hsafeInt color.val
  have hbodyL1 : (∑ color, |B color - 1 / (Parameters.modulus parameter : ℝ)|) ≤
      4 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter := by
    simpa only [B, bodyMean, Int.cast_natCast, one_div] using TrimmedSlice.blurredSafeLaw_palette_l1_le
      (Parameters.modulus parameter) (Parameters.safeMargin parameter) (bodyShifts parameter) (bodyLaw parameter).weight
      (by positivity) (bodyLaw parameter).sum_one (bodyLaw parameter).nonneg hsafeInt hshifts
  have hrL1 := referenceMean_l1_le parameter cutoffScale (beta parameter) (boundary parameter) hscale hlarge hm.2.2.1 hm.2.2.2
  have hcard : ((boundaryPalette (Parameters.modulus parameter) (boundary parameter)).card : ℝ) ≤
      2 * Parameters.safeMargin parameter := by
    have hh := boundaryPalette_card (Parameters.modulus parameter) (boundary parameter) hm.1.1.1
      (by have hh := hm.1.1.2; omega)
    have hh' : ((boundaryPalette (Parameters.modulus parameter) (boundary parameter)).card : ℝ) = 2 * boundary parameter := by exact_mod_cast hh
    rw [hh']
    exact_mod_cast (show 2 * boundary parameter ≤ 2 * (Parameters.safeMargin parameter : ℤ) by linarith [hm.1.1.2])
  have hrL1' : (∑ color, |r color - 1 / (Parameters.modulus parameter : ℝ)|) ≤
      4 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter := by
    apply hrL1.trans
    apply div_le_div_of_nonneg_right _ hq.le
    linarith
  have hfringe : (∑ color, |B color - r color|) ≤
      8 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter := by
    calc
      _ ≤ ∑ color, (|B color - 1 / (Parameters.modulus parameter : ℝ)| +
          |r color - 1 / (Parameters.modulus parameter : ℝ)|) := by
        apply Finset.sum_le_sum
        intro color _
        simpa only [abs_sub_comm (1 / (Parameters.modulus parameter : ℝ)) (r color)] using
          abs_sub_le (B color) (1 / (Parameters.modulus parameter : ℝ)) (r color)
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        exact (add_le_add hbodyL1 hrL1').trans_eq (by ring)
  have hb := body_reference_mean_bounds B base p r (1 / (Parameters.modulus parameter : ℝ))
    (1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter))
    (bodyCompensation parameter cutoffScale)
    ((Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter / Parameters.dimension parameter)
    (8 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter)
    (by positivity) (by positivity)
    (div_le_div_of_nonneg_left (mul_nonneg hm0 ha.le) hN hpop) hp0
    (by intro color; convert hp.1 color using 1; ring)
    (by intro color; exact ⟨lt_of_lt_of_le (by positivity) (hbase.1 color) |>.le, by linarith [hhalf color]⟩)
    (fun color => ⟨hbody0 color, hbodyUpper color⟩) hdef
    (one_div_le_one_div_of_le hsafe (by linarith))
    (fun color => referenceMean_primary_difference parameter cutoffScale (beta parameter) (boundary parameter)
      (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
      (sources parameter) (sourceLaw parameter) color) hfringe
  have heq : 4 * (1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) -
      1 / (Parameters.modulus parameter : ℝ)) / (1 / (Parameters.modulus parameter : ℝ)) =
      8 * (Parameters.safeMargin parameter : ℝ) /
        ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) := by
    field_simp
    ring
  simpa only [heq] using hb

end

end AFT.V7Calibration

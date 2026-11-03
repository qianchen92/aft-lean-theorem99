import AFT.BetaPrimaryCalibration

/-!
# The actual beta-calibrated V7 primary probability and sign response
-/

namespace AFT

open Filter
open scoped BigOperators Topology

theorem uniformFiniteProfile_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (support : Finset ι) (hne : support.Nonempty) :
    ∑ color, uniformFiniteProfile support color = 1 := by
  have hh : (support.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hne.card_pos
  simp [uniformFiniteProfile, hh]

namespace V7Calibration

noncomputable def repairedBoundaryMass (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ) : ℝ :=
  ((boundaryPalette (Parameters.modulus parameter) boundary).card / (Parameters.modulus parameter : ℝ)) /
    (GaussianSource.v7Activation cutoffScale parameter * beta)

noncomputable def primary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  calibratedPrimaryProfile (basePrimary parameter cutoffScale boundary bodyShifts bodyLaw
    startsPlus startsMinus sources sourceLaw)
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary))
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ)
    (repairedBoundaryMass parameter cutoffScale beta boundary - v7BaseBoundaryMass cutoffScale parameter boundary)

/-- The exact finite beta repair gives a probability law bounded below by
`1/(4q)`, and preserves the concrete sign estimates needed by the inverse. -/
theorem primary_estimates_eventually {σ τ : ℕ → Type*}
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
      let v := signResponse parameter cutoffScale (boundary parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter) (sourceLaw parameter)
      (∀ color, 1 / (4 * (Parameters.modulus parameter : ℝ)) ≤ p color) ∧
      (∀ color, |v color| ≤ (2 * GaussianSource.v7Activation cutoffScale parameter) * p color) ∧
      (∑ color, |v color|) ≤ 32 * ((Parameters.anchorWidth parameter : ℝ) / Parameters.modulus parameter) ∧
      (∑ color, v color) = 0 ∧ (∑ color, p color) = 1 := by
  have hs := hmodel.mono fun _ h => h.1
  have hb := hs.mono fun _ h => h.1
  filter_upwards [hmodel, base_sign_estimates_eventually cutoffScale hscale boundary bodyShifts bodyLaw
    startsPlus startsMinus sources sourceLaw hs, v7_boundary_debit_eventually cutoffScale hscale boundary hb,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary hb, eventually_ge_atTop 2]
    with parameter hm he hdebit hclear hlarge
  dsimp only at he ⊢
  have hq : 0 < (Parameters.modulus parameter : ℝ) := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hqInt : (0 : ℤ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hx : 0 < Parameters.security parameter := lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hlegs : 0 < (Parameters.legs parameter : ℝ) := by unfold Parameters.legs; positivity
  have hdim : 0 < (Parameters.dimension parameter : ℝ) := by
    exact_mod_cast Nat.mul_pos (Parameters.modulus_prime parameter).pos (pow_pos hx 20)
  have ha : 0 < GaussianSource.v7Activation cutoffScale parameter :=
    GaussianSource.activation_positive _ _ _ _ (GaussianSource.legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have hpopulation : (Parameters.bodies parameter : ℝ) + 2 * Parameters.legs parameter = Parameters.dimension parameter := by
    exact_mod_cast Parameters.population_identity parameter
  have hmassBounds : v7BaseBoundaryMass cutoffScale parameter (boundary parameter) / 2 ≤
      repairedBoundaryMass parameter cutoffScale (beta parameter) (boundary parameter) ∧
      repairedBoundaryMass parameter cutoffScale (beta parameter) (boundary parameter) ≤
        2 * v7BaseBoundaryMass cutoffScale parameter (boundary parameter) := by
    have hh := beta_boundary_mass_bounds (Parameters.dimension parameter) (Parameters.legs parameter)
      (GaussianSource.v7Activation cutoffScale parameter)
      ((boundaryPalette (Parameters.modulus parameter) (boundary parameter)).card / (Parameters.modulus parameter : ℝ))
      (beta parameter) hdim hlegs ha (by positivity) hm.2.2.1 hm.2.2.2
    have heq : (Parameters.dimension parameter : ℝ) *
        ((boundaryPalette (Parameters.modulus parameter) (boundary parameter)).card / (Parameters.modulus parameter : ℝ)) /
        (Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter) =
        v7BaseBoundaryMass cutoffScale parameter (boundary parameter) := by
      unfold v7BaseBoundaryMass
      ring
    simpa only [repairedBoundaryMass, heq] using hh
  have hhalf := betaPrimaryRepair_ge_half (boundaryPalette (Parameters.modulus parameter) (boundary parameter))
    (basePrimary parameter cutoffScale (boundary parameter) (bodyShifts parameter) (bodyLaw parameter)
      (startsPlus parameter) (startsMinus parameter) (sources parameter) (sourceLaw parameter))
    (v7BaseBoundaryMass cutoffScale parameter (boundary parameter))
    (repairedBoundaryMass parameter cutoffScale (beta parameter) (boundary parameter)) hmassBounds.1 hmassBounds.2
    (by
      intro color hc
      have hout := (mem_boundaryPalette _ _ color).mp hc
      have hcard : ((boundaryPalette (Parameters.modulus parameter) (boundary parameter)).card : ℝ) ≠ 0 := by
        exact_mod_cast ne_of_gt (Finset.card_pos.mpr ⟨color, hc⟩)
      unfold basePrimary
      rw [TrimmedSlice.actualFairBasePrimary_eq_average]
      have hbnd (starts : τ parameter → ℤ) := TrimmedSlice.actualBasePrimary_boundary
        (Parameters.modulus parameter) (Parameters.safeMargin parameter) (boundary parameter)
        (Parameters.anchorWidth parameter) (Parameters.bodies parameter) (Parameters.legs parameter)
        (GaussianSource.v7Activation cutoffScale parameter) (bodyShifts parameter) (bodyLaw parameter).weight
        starts (sources parameter) (sourceLaw parameter).weight (by omega) hm.2.1 color.val hout
      rw [hbnd, hbnd]
      rw [hpopulation]
      simp only [Int.cast_natCast, v7BaseBoundaryMass]
      field_simp
      ring)
    (by intro color _; exact hdebit.trans (he.1 color))
  have hbaseMass : ∑ color, basePrimary parameter cutoffScale (boundary parameter)
      (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
      (sources parameter) (sourceLaw parameter) color = 1 := by
    exact TrimmedSlice.actualFairBasePrimary_palette_mass (Parameters.modulus parameter)
      (Parameters.safeMargin parameter) (boundary parameter) (3 * Parameters.anchorWidth parameter)
      (GaussianSource.legCutoff cutoffScale parameter) (Parameters.anchorWidth parameter)
      (Parameters.bodies parameter) (Parameters.legs parameter) (GaussianSource.v7Activation cutoffScale parameter)
      (bodyShifts parameter) (bodyLaw parameter).weight (startsPlus parameter) (startsMinus parameter)
      (sources parameter) (sourceLaw parameter).weight (ne_of_gt (Parameters.modulus_prime parameter).pos)
      (ne_of_gt (mul_pos hlegs ha)) (pow_ne_zero _ (ne_of_gt hx))
      (bodyLaw parameter).sum_one (by omega)
      (by intro index; have hbzero := hm.1.1.1; exact (hm.2.1 index).trans (by omega))
      (sourceLaw parameter).sum_one hm.1.1.1 (by positivity) hm.1.2.1 hm.1.2.2.1 hm.1.2.2.2 (by omega)
  refine ⟨?_, ?_, he.2.2.1, he.2.2.2, ?_⟩
  · intro color
    have hh := he.1 color
    have hh' := hhalf color
    change _ ≤ primary parameter cutoffScale (beta parameter) (boundary parameter)
      (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
      (sources parameter) (sourceLaw parameter) color at hh'
    calc
      _ = (1 / (2 * (Parameters.modulus parameter : ℝ))) / 2 := by ring
      _ ≤ _ := (div_le_div_of_nonneg_right hh (by norm_num)).trans hh'
  · intro color
    have hh := mul_le_mul_of_nonneg_left (hhalf color) ha.le
    exact (he.2.1 color).trans (by dsimp only [primary]; nlinarith only [hh])
  · by_cases hboundary : (boundaryPalette (Parameters.modulus parameter) (boundary parameter)).Nonempty
    · have hinterior : (boundaryPalette (Parameters.modulus parameter) (boundary parameter))ᶜ.Nonempty := by
        rw [boundaryPalette, compl_compl]
        exact TrimmedSlice.paletteSlice_nonempty _ _ _ hm.1.1.1 (by simp only [abs_zero]; omega)
      exact calibratedPrimaryProfile_mass _ _ _ _ hbaseMass
        (uniformFiniteProfile_mass _ hboundary) (uniformFiniteProfile_mass _ hinterior)
    · have hempty : boundaryPalette (Parameters.modulus parameter) (boundary parameter) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hboundary
      simpa only [primary, repairedBoundaryMass, v7BaseBoundaryMass, hempty, Finset.card_empty,
        Nat.cast_zero, zero_div, mul_zero, sub_self, calibratedPrimaryProfile, zero_smul, add_zero]
        using hbaseMass

end V7Calibration
end AFT

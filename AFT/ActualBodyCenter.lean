import AFT.AnchorSeed

/-! # The actual positive, calibrated safe-center probability -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def safePalette (parameter : ℕ) : Finset (Fin (Parameters.modulus parameter)) :=
  TrimmedSlice.paletteSlice (Parameters.modulus parameter) (Parameters.safeMargin parameter) 0

theorem safePalette_nonempty (parameter : ℕ) : (safePalette parameter).Nonempty := by
  apply TrimmedSlice.paletteSlice_nonempty _ _ _ (by positivity)
  have hh := Parameters.safeSize_positive parameter
  unfold Parameters.safeSize at hh
  simp only [abs_zero, add_zero]
  omega

def actualCoreLaw (parameter : ℕ) : FiniteDist (Fin (Parameters.modulus parameter)) :=
  FiniteDist.uniformSafe (safePalette parameter) (safePalette_nonempty parameter)

theorem actualCoreLaw_weight (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) :
    (actualCoreLaw parameter).weight color = uniformFiniteProfile (safePalette parameter) color := by
  by_cases hc : color ∈ safePalette parameter <;> simp [actualCoreLaw, FiniteDist.uniformSafe, uniformFiniteProfile, hc]

theorem safeMargin_le_anchor (parameter : ℕ) : Parameters.safeMargin parameter ≤ Parameters.anchorWidth parameter := by
  have hh : 20 ≤ Parameters.security parameter ^ 30 := by
    have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 30
    omega
  have hh' := Nat.mul_le_mul_right (Parameters.security parameter ^ 2) hh
  simpa only [Parameters.safeMargin, Parameters.anchorWidth, ← pow_add] using hh'

theorem actual_anchor_safe_mass (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) :
    (∑ output : Fin (Parameters.modulus parameter), publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      color output.val) = 1 ∧
    (∀ output : Fin (Parameters.modulus parameter), output ∉ safePalette parameter →
      publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output.val = 0) := by
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact ne_of_gt (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)) 32)
  have hh := publicAnchorKernel_safe_mass (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (Parameters.safeMargin parameter) 0 hw (Parameters.anchor_clearance parameter) (by positivity)
    (by simpa only [abs_zero, add_zero] using (show (Parameters.safeMargin parameter : ℤ) ≤ Parameters.anchorWidth parameter by exact_mod_cast safeMargin_le_anchor parameter)) color
  refine ⟨hh.1, ?_⟩
  intro output hout
  apply hh.2 output.val
  simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
    TrimmedSlice.mem_slice] at hout
  omega

theorem actual_primary_probability_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∀ color, 0 < actualPrimary cutoffScale parameter (beta parameter) color) ∧
      (∑ color, actualPrimary cutoffScale parameter (beta parameter) color) = 1 := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel] with parameter hp
  dsimp only at hp
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  exact ⟨fun color => lt_of_lt_of_le (by positivity) (hp.1 color), hp.2.2.2.2⟩

/-- The actual compensated center profile, including the calibrated primary. -/
def actualBodyCenter (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) : Fin (Parameters.modulus parameter) → ℝ :=
  calibratedBodyProfile (actualCoreLaw parameter).weight
    (fun center => anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (actualPrimary cutoffScale parameter beta) center.val)
    (bodyCompensation parameter cutoffScale)

theorem legs_fraction_small (parameter : ℕ) : (Parameters.legs parameter : ℝ) / Parameters.bodies parameter ≤ 1 / 772 := by
  have hh : 774 ≤ Parameters.security parameter ^ 30 := by
    have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 30
    omega
  have hlarge : 774 * Parameters.legs parameter ≤ Parameters.dimension parameter := by
    have hmul := Nat.mul_le_mul_right (Parameters.security parameter ^ 30) hh
    have hh' : 774 * Parameters.legs parameter ≤ Parameters.security parameter ^ 60 := by
      simpa only [Parameters.legs, ← pow_add] using hmul
    exact hh'.trans (Parameters.dimension_bounds parameter).1
  have hpop := Parameters.population_identity parameter
  have hbound : 772 * Parameters.legs parameter ≤ Parameters.bodies parameter := by omega
  have hb : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  apply (div_le_div_iff₀ hb (by norm_num : (0 : ℝ) < 772)).mpr
  have hh : (Parameters.legs parameter : ℝ) * 772 ≤ 1 * Parameters.bodies parameter := by
    simpa only [mul_comm, one_mul] using (show (772 : ℝ) * Parameters.legs parameter ≤ Parameters.bodies parameter by exact_mod_cast hbound)
  exact hh

/-- The true body-center profile is a probability on the safe palette,
and is uniformly comparable to its actual core law. -/
theorem actual_body_center_probability_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∑ center, actualBodyCenter cutoffScale parameter (beta parameter) center) = 1 ∧
      (∀ center, (actualCoreLaw parameter).weight center / 2 ≤ actualBodyCenter cutoffScale parameter (beta parameter) center ∧
        actualBodyCenter cutoffScale parameter (beta parameter) center ≤ 2 * (actualCoreLaw parameter).weight center) ∧
      (∀ center, center ∉ safePalette parameter → actualBodyCenter cutoffScale parameter (beta parameter) center = 0) := by
  filter_upwards [actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_anchor_bound_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hp hanchor hlarge
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let anchor : Fin (Parameters.modulus parameter) → ℝ := fun center => anchorMean (Parameters.modulus parameter)
    (Parameters.anchorWidth parameter) p center.val
  let core := (actualCoreLaw parameter).weight
  let delta := bodyCompensation parameter cutoffScale
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hN : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  have ha : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have ha1 : v7Activation cutoffScale parameter ≤ 1 := (activation_le_one_hundredth _ _ _ _).trans (by norm_num)
  have hd0 : 0 ≤ delta := by dsimp [delta, bodyCompensation]; positivity
  have hd1 : delta ≤ 1 := by
    have hh := legs_fraction_small parameter
    have heq : delta = ((Parameters.legs parameter : ℝ) / Parameters.bodies parameter) * v7Activation cutoffScale parameter := by dsimp [delta, bodyCompensation]; ring
    rw [heq]
    have ht := mul_le_mul hh ha1 ha.le (by norm_num : (0 : ℝ) ≤ 1 / 772)
    linarith
  have ha0 (center) : 0 ≤ anchor center := by
    exact Finset.sum_nonneg fun color _ => mul_nonneg (hp.1 color).le (publicAnchorKernel_nonneg _ _ _ _)
  have haMass : ∑ center, anchor center = 1 := by
    dsimp only [anchor, anchorMean]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (actual_anchor_safe_mass parameter _).1, mul_one]
    exact hp.2
  have haOutside (center) (hout : center ∉ safePalette parameter) : anchor center = 0 := by
    dsimp only [anchor, anchorMean]
    simp_rw [(actual_anchor_safe_mass parameter _).2 center hout, mul_zero, Finset.sum_const_zero]
  have hc0 (center) : 0 ≤ core center := (actualCoreLaw parameter).nonneg center
  have hcore (center) (hin : center ∈ safePalette parameter) : 1 / (Parameters.modulus parameter : ℝ) ≤ core center := by
    have hc : (0 : ℝ) < (safePalette parameter).card := by exact_mod_cast (safePalette_nonempty parameter).card_pos
    have hcard : ((safePalette parameter).card : ℝ) ≤ Parameters.modulus parameter := by
      exact_mod_cast (show (safePalette parameter).card ≤ Parameters.modulus parameter by simpa only [Fintype.card_fin] using Finset.card_le_univ (safePalette parameter))
    simpa only [core, actualCoreLaw, FiniteDist.uniformSafe, if_pos hin, one_div] using
      one_div_le_one_div_of_le hc hcard
  have hdebit (center) : delta * anchor center ≤ 1 / (2 * (Parameters.modulus parameter : ℝ)) := by
    have heq : delta * anchor center = ((Parameters.legs parameter : ℝ) / Parameters.bodies parameter) *
        (v7Activation cutoffScale parameter * anchor center) := by dsimp [delta, bodyCompensation]; ring
    rw [heq]
    have hh := mul_le_mul (legs_fraction_small parameter) (hanchor center.val)
      (mul_nonneg ha.le (ha0 center)) (by norm_num : (0 : ℝ) ≤ 1 / 772)
    exact hh.trans_eq (by ring)
  have hpoint (center) : core center / 2 ≤ actualBodyCenter cutoffScale parameter (beta parameter) center ∧
      actualBodyCenter cutoffScale parameter (beta parameter) center ≤ 2 * core center := by
    change core center / 2 ≤ (1 + delta) * core center - delta * anchor center ∧
      (1 + delta) * core center - delta * anchor center ≤ 2 * core center
    by_cases hin : center ∈ safePalette parameter
    · have hh := hcore center hin
      have hd := hdebit center
      have heq : 1 / (2 * (Parameters.modulus parameter : ℝ)) = (1 / (Parameters.modulus parameter : ℝ)) / 2 := by ring
      rw [heq] at hd
      constructor <;> nlinarith [hc0 center, ha0 center]
    · have hc : core center = 0 := by simp [core, actualCoreLaw, FiniteDist.uniformSafe, hin]
      rw [hc, haOutside center hin]
      norm_num
      exact le_rfl
  refine ⟨?_, hpoint, ?_⟩
  · exact calibratedBodyProfile_mass core anchor delta (actualCoreLaw parameter).sum_one haMass
  · intro center hout
    have hc : core center = 0 := by simp [core, actualCoreLaw, FiniteDist.uniformSafe, hout]
    have hh := hpoint center
    rw [hc] at hh
    simp only [zero_div, mul_zero] at hh
    exact le_antisymm hh.2 hh.1

end
end AFT.V7Calibration

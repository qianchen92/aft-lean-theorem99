import AFT.ActualBackgroundBoundary
import AFT.BoundaryCollapseChange
import AFT.PrimaryLawLower

/-! # Uniform-interior boundary collapse in the actual primary Hilbert norm -/
namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem actual_interior_profile_upper_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ color,0≤actualInteriorProfile C n color ∧
      actualInteriorProfile C n color≤2/(Parameters.modulus n : ℝ) := by
  filter_upwards [body_support_scales_eventually C hC] with n hs color
  have hq : (0 : ℝ)<Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
  let boundary := boundaryPalette (Parameters.modulus n) (boundaryHalf C n)
  have hsmall : 2*(boundary.card : ℝ)≤Parameters.modulus n := by
    have hmargin := safeMargin_quarter n
    have hcard := boundaryPalette_card (Parameters.modulus n) (boundaryHalf C n) hs.2.2.1
      (by have hh := hs.2.2.2; omega)
    have hcard' : (boundary.card : ℝ)≤2*Parameters.safeMargin n := by
      have hh : (boundary.card : ℝ)=2*boundaryHalf C n := by exact_mod_cast hcard
      rw [hh]
      exact_mod_cast (show 2*boundaryHalf C n≤2*(Parameters.safeMargin n : ℤ) by linarith [hs.2.2.2])
    have hh : (4 : ℝ)*Parameters.safeMargin n≤Parameters.modulus n := by exact_mod_cast hmargin
    linarith
  have hc : (boundary.card : ℝ)+boundaryᶜ.card=Parameters.modulus n := by
    exact_mod_cast (show boundary.card+boundaryᶜ.card=Parameters.modulus n by
      simpa only [Fintype.card_fin] using boundary.card_add_card_compl)
  have hi : (0 : ℝ)<boundaryᶜ.card := by linarith
  change 0≤uniformFiniteProfile boundaryᶜ color ∧ uniformFiniteProfile boundaryᶜ color≤_
  unfold uniformFiniteProfile
  split_ifs
  · constructor
    · positivity
    · rw [← one_div]
      apply (div_le_div_iff₀ hi hq).mpr
      linarith
  · exact ⟨le_rfl,by positivity⟩

theorem actual_boundary_normalizer_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      (∀ color,0<(actualPrimaryLaw C n (beta n)).weight color) ∧
      (∑ color∈(boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ,
        (actualPrimaryLaw C n (beta n)).weight color)≠0 ∧
      ∀ color,|boundaryNormalizerFactor
        (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
        (actualPrimaryLaw C n (beta n)).weight (actualInteriorProfile C n) color|≤8 := by
  filter_upwards [actual_interior_profile_upper_eventually C hC,
    actual_interior_collapse_properties_eventually C hC,
    actual_boundary_profiles_eventually C hC,
    actual_primary_law_quarter_lower_eventually C hC beta hbeta] with n hu hi hb hp
  have hq : (0 : ℝ)<Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
  have hpos (color) : 0<(actualPrimaryLaw C n (beta n)).weight color :=
    (by positivity : (0 : ℝ)<1/(4*(Parameters.modulus n : ℝ))).trans_le (hp color)
  let interior := (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
  have hmass0 : 0<(∑ color∈interior,(actualPrimaryLaw C n (beta n)).weight color) :=
    Finset.sum_pos (fun color _ => hpos color) hb.2.1
  have hmass1 : (∑ color∈interior,(actualPrimaryLaw C n (beta n)).weight color)≤1 := by
    rw [← (actualPrimaryLaw C n (beta n)).sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun color _ _ => (actualPrimaryLaw C n (beta n)).nonneg color)
  refine ⟨hpos,hmass0.ne',?_⟩
  intro color
  unfold boundaryNormalizerFactor
  split_ifs with hc
  · rw [hi.2,one_mul,abs_of_nonneg (div_nonneg (mul_nonneg hmass0.le (hu color).1) (hpos color).le)]
    apply (div_le_iff₀ (hpos color)).mpr
    have hnum : (∑ point∈interior,(actualPrimaryLaw C n (beta n)).weight point)*
        actualInteriorProfile C n color≤2/(Parameters.modulus n : ℝ) :=
      (mul_le_mul_of_nonneg_right hmass1 (hu color).1).trans (by simpa only [one_mul] using (hu color).2)
    have hlow := mul_le_mul_of_nonneg_left (hp color) (by norm_num : (0 : ℝ)≤8)
    have he : 8*(1/(4*(Parameters.modulus n : ℝ)))=2/(Parameters.modulus n : ℝ) := by ring
    rw [he] at hlow
    exact hnum.trans hlow
  · norm_num

theorem actual_boundary_collapse_mixed_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ (Slot : Type*) [Fintype Slot] [DecidableEq Slot],
      ∀ reference : Slot → FiniteDist (Fin (Parameters.modulus n)),∀ rates : Slot → ℝ,
      (∀ slot,0≤rates slot) →∀ slot,0<rates slot → reference slot=actualPrimaryLaw C n (beta n) →
      ∀ kernel, MixedKernel.activity rates reference
        (MixedKernel.partialInputOperator slot
          (boundaryCollapse (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ (actualInteriorProfile C n))
          (reference slot).weight kernel)≤16*MixedKernel.activity rates reference kernel := by
  filter_upwards [actual_boundary_normalizer_eventually C hC beta hbeta]
    with n hn Slot instFintype instDecEq reference rates hrates slot hrate href kernel
  have hp : ∀ color,0<(reference slot).weight color := by rw [href]; exact hn.1
  have hm : (∑ color∈(boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ,
      (reference slot).weight color)≠0 := by rw [href]; exact hn.2.1
  have hf : ∀ color,|boundaryNormalizerFactor
      (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
      (reference slot).weight (actualInteriorProfile C n) color|≤8 := by rw [href]; exact hn.2.2
  simpa only [show (2 : ℝ)*8=16 by norm_num] using
    MixedKernel.boundaryCollapse_change_activity_le reference rates hrates slot hrate _ _
      hp hm 8 (by norm_num) hf kernel

end
end AFT.V7Calibration

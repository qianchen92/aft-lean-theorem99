import AFT.JointMixedOutput
import AFT.SafeBodyOutput
import AFT.MarkedFringe

/-! # Actual canonical marked mixed seed and its exact leading output -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

theorem mixed_pair_canonical (primary body : FiniteDist Color) (kernel : Color → Color → ℝ)
    (hrow : ∀ first, (∑ center,body.weight center*kernel first center) = 0)
    (hcol : ∀ center, (∑ first,primary.weight first*kernel first center) = 0) :
    Hoeffding.Canonical (pairReference primary body) Finset.univ (pairKernel kernel) := by
  constructor
  · intro x y hxy
    exact congrArg (pairKernel kernel) (funext fun slot => hxy slot (Finset.mem_univ slot))
  · intro slot _ word
    fin_cases slot
    · simpa [pairReference,pairKernel,Function.update,Fin.ext_iff] using hcol (word 1)
    · simpa [pairReference,pairKernel,Function.update,Fin.ext_iff] using hrow (word 0)

end
end AFT.MixedKernel

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Recovering the true signed safe mass is valid also at zero body atoms. -/
theorem actual_marked_safe_density_mass_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ first center,
      (actualPrimaryLaw C n (beta n)).weight first*(actualBodyLaw C n (beta n)).weight center*
        actualMarkedSafeDensity C n (beta n) first center = actualMarkedSafeSeed C n (beta n) first center := by
  filter_upwards [actual_primary_probability_eventually C hC beta hbeta,
    actual_body_safe_lower_eventually C hC beta hbeta,
    actual_marked_safe_canonical_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta] with n hp hb hs hl first center
  rw [hl.1,hl.2.1]
  by_cases hz : actualBodyCenter C n (beta n) center = 0
  · have hout : center ∉ safePalette n := by
      intro hi
      have hh := hb center hi
      rw [hl.2.1,hz] at hh
      have hq : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
      have hpos : (0 : ℝ) < 1/(2*(Parameters.modulus n : ℝ)) := by positivity
      linarith
    rw [hs.2.2 first center hout,hz,mul_zero,zero_mul]
  · unfold actualMarkedSafeDensity
    field_simp [(hp.1 first).ne',hz]

theorem actual_marked_input_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualMarkedInput C n (beta n))) Finset.univ (actualMarkedInput C n (beta n)).kernel := by
  filter_upwards [actual_marked_safe_density_mass_eventually C hC beta hbeta,
    actual_marked_safe_canonical_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta] with n hm hs hp hl
  have href : inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (actualMarkedInput C n (beta n)) = MixedKernel.pairReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) := by
    funext slot
    fin_cases slot <;> rfl
  rw [href]
  dsimp only [actualMarkedInput]
  apply MixedKernel.mixed_pair_canonical
  · intro first
    have hp0 : (actualPrimaryLaw C n (beta n)).weight first ≠ 0 := by rw [hl.1]; exact (hp.1 _).ne'
    calc
      _ = (∑ color, actualMarkedSafeSeed C n (beta n) first color)/(actualPrimaryLaw C n (beta n)).weight first := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro color _
        have h := hm first color
        field_simp [hp0]
        nlinarith [h]
      _ = 0 := by rw [hs.1,zero_div]
  · intro center
    by_cases hz : (actualBodyLaw C n (beta n)).weight center = 0
    · rw [hl.2.1] at hz
      simp only [actualMarkedSafeDensity,hz,mul_zero,div_zero,Finset.sum_const_zero]
    · calc
        _ = (∑ color, actualMarkedSafeSeed C n (beta n) color center)/(actualBodyLaw C n (beta n)).weight center := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro color _
          have h := hm color center
          field_simp [hz]
          nlinarith [h]
        _ = 0 := by rw [hs.2.1,zero_div]

/-- The genuine mixed inverse and body channel recover exactly the integer
root image of the safe marked pair seed. -/
theorem actual_marked_inverse_outputMass_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ output : Fin 2 → Fin (Parameters.modulus n),
      seedOutputMass (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualPrimaryChannel C n) (actualBodyChannel n)
        (inversePrimarySeed (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (actualMarkedInput C n (beta n))) output =
      rootProfileOperator n (actualMarkedSafeSeed C n (beta n) (output 0)) (output 1) := by
  filter_upwards [actual_marked_safe_density_mass_eventually C hC beta hbeta,
    actual_marked_safe_canonical_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n hm hs hp hl hn operator hop output
  have hp0 (color) : (actualPrimaryLaw C n (beta n)).weight color ≠ 0 := by rw [hl.1]; exact (hp.1 _).ne'
  have hrho : v7Activation C n ≠ 0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).ne'
  dsimp only [actualMarkedInput]
  rw [actual_inverse_mixed_pair_outputMass C n (beta n) operator hop hrho hp0]
  change (∑ center, (actualPrimaryLaw C n (beta n)).weight (output 0)*(actualBodyLaw C n (beta n)).weight center*
    actualMarkedSafeDensity C n (beta n) (output 0) center*actualBodyChannel n center (output 1)) = _
  simp_rw [hm]
  rw [actualBodyChannel_profile,safe_root_convolution_eq n _ (hs.2.2 (output 0))]
  simp only [v7RootCutoff,Parameters.safeMargin,Parameters.security_eq n hn]
  omega

end
end AFT.V7Calibration

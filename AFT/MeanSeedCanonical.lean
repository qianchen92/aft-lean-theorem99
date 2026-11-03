import AFT.MeanOutput
import AFT.PrimarySeedCanonical

/-! # Actual canonicality of every one-coordinate background mean input -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

theorem primarySingletonInput_canonical (primary body : FiniteDist Color) (kernel : Color → ℝ)
    (h : ∑ color, primary.weight color*kernel color = 0) :
    Hoeffding.Canonical (inputReference primary body (primarySingletonInput kernel)) Finset.univ
      (primarySingletonInput kernel).kernel := by
  dsimp only [primarySingletonInput]
  constructor
  · intro x y heq
    exact congrArg kernel (heq 0 (Finset.mem_univ 0))
  · intro slot _ word
    fin_cases slot
    simpa [inputReference,Fin.addCases,MixedKernel.singletonKernel] using h

theorem bodySingletonInput_canonical (primary body : FiniteDist Color) (kernel : Color → ℝ)
    (h : ∑ color, body.weight color*kernel color = 0) :
    Hoeffding.Canonical (inputReference primary body (bodySingletonInput kernel)) Finset.univ
      (bodySingletonInput kernel).kernel := by
  dsimp only [bodySingletonInput]
  constructor
  · intro x y heq
    exact congrArg kernel (heq 0 (Finset.mem_univ 0))
  · intro slot _ word
    fin_cases slot
    simpa [inputReference,Fin.addCases,MixedKernel.singletonKernel] using h

theorem profile_density_mass (reference profile : Color → ℝ)
    (hrecover : ∀ color, reference color*(profile color/reference color) = profile color)
    (hmass : ∑ color, profile color = 0) :
    (∑ color, reference color*(profile color/reference color)) = 0 := by
  simp_rw [hrecover]
  exact hmass

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

/-- The full population blur of the original safe core is a real probability
profile on the integer palette, with no discarded boundary mass. -/
theorem actual_body_mean_mass_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n : ℕ in atTop, (∑ color,actualBodyMean C n color) = 1 := by
  filter_upwards [body_support_scales_eventually C hC] with n hs
  apply TrimmedSlice.blurredSafeLaw_palette_mass _ _ _ _ (bodyBlur C n).sum_one
  · have hh := Parameters.safeSize_positive n
    unfold Parameters.safeSize at hh
    omega
  · intro sample
    exact (bodyShift_abs_le C n sample).trans (by exact_mod_cast hs.1)

/-- These are the exact five mean seeds used by the literal background
certificate, including its genuine safe-body seeds and primary fringes. -/
theorem actual_mean_seeds_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      let p := actualPrimaryLaw C n (beta n)
      let b := actualBodyLaw C n (beta n)
      let canonical := fun seed : InputSeed (Fin (Parameters.modulus n)) =>
        Hoeffding.Canonical (inputReference p b seed) Finset.univ seed.kernel
      canonical (rootMeanInput C n (beta n)) ∧ canonical (fullBodyMeanInput C n (beta n)) ∧
      canonical (extraAnchorMeanInput C n (beta n)) ∧
      ∀ shift : ℤ, |shift| ≤ maxBodyShift C n →
        canonical (bodyMeanSafeInput C n (beta n) shift) ∧ canonical (bodyMeanOutsideInput C n (beta n) shift) := by
  filter_upwards [actual_body_type_power_bounds C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,
    actual_reference_probability_eventually C hC beta hbeta,
    actual_extra_anchor_seed_bounds C hC beta hbeta,
    actual_extra_anchor_seed_power_bounds C hC beta hbeta,
    actual_body_mean_mass_eventually C hC,eventually_ge_atTop 2]
    with n ht hl hp hr he hep hf hn
  dsimp only
  have hprimary (profile : Fin (Parameters.modulus n) → ℝ) (hmass : ∑ color,profile color = 0) :
      Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (primarySingletonInput (fun color => profile color/actualPrimary C n (beta n) color))) Finset.univ
        (primarySingletonInput (fun color => profile color/actualPrimary C n (beta n) color)).kernel := by
    apply primarySingletonInput_canonical
    rw [hl.1]
    exact profile_density_mass _ _ (fun color => by field_simp [(hp.1 color).ne']) hmass
  refine ⟨?_,?_,?_,?_⟩
  · apply hprimary
    rw [Finset.sum_sub_distrib,actual_root_body_mean_mass n hn,hr.2,sub_self]
  · apply hprimary
    rw [Finset.sum_sub_distrib,hf,hr.2,sub_self]
  · apply bodySingletonInput_canonical
    rw [hl.2.1]
    exact profile_density_mass _ _ (profile_weight_recover _ _ (8*(n : ℝ)^8) hep.2) he.1
  · intro shift hs
    have ht := ht shift hs
    constructor
    · apply bodySingletonInput_canonical
      rw [hl.2.1]
      exact profile_density_mass _ _ (profile_weight_recover _ _ 5 ht.2.2.1) ht.1
    · exact hprimary _ ht.2.2.2.2.1

end
end AFT.V7Calibration

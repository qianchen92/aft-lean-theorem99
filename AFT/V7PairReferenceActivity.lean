import AFT.V7PairReferenceChange

/-! # The genuine reference correction as a literal calibrated input seed -/

namespace AFT.V7Calibration

open GaussianSource SafeConvolution Filter
open scoped BigOperators Classical Topology

noncomputable section
attribute [local instance] actualModulusNeZero

/-- A literal two-primary seed, retaining its actual joint density. -/
def primaryPairSeed {Color : Type*} (kernel : (Fin 2 → Color) → ℝ) :
    RepresentedPolynomial.InputSeed Color where
  primaryOrder := 2
  bodyOrder := 0
  kernel := kernel

theorem primaryPairSeed_weight {Color : Type*} [Fintype Color]
    (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (kernel : (Fin 2 → Color) → ℝ) :
    RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius (primaryPairSeed kernel) =
      MixedKernel.activity ![(Real.sqrt primaryPool)⁻¹,(Real.sqrt primaryPool)⁻¹]
        (MixedKernel.pairReference primary primary) kernel := by
  have hrate : RepresentedPolynomial.inputRate primaryPool bodyPool (primaryPairSeed kernel) =
      ![(Real.sqrt primaryPool)⁻¹,(Real.sqrt primaryPool)⁻¹] := by funext i; fin_cases i <;> rfl
  have href : RepresentedPolynomial.inputReference primary body (primaryPairSeed kernel) =
      MixedKernel.pairReference primary primary := by funext i; fin_cases i <;> rfl
  unfold RepresentedPolynomial.inputWeight MixedKernel.analyticActivity
  rw [hrate, href]
  simp only [primaryPairSeed, pow_zero, one_mul]
  rfl

def actualPairReferenceInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) :=
  primaryPairSeed (MixedKernel.pairKernel (fun x y =>
    (v7Activation cutoffScale parameter ^ 2)⁻¹ * actualPairReferenceChange cutoffScale parameter beta (x,y) /
      ((actualPrimaryLaw cutoffScale parameter beta).weight x * (actualPrimaryLaw cutoffScale parameter beta).weight y)))

def pairReferenceMixedConstant (cutoffScale : ℝ) : ℝ :=
  activationConstant cutoffScale ^ 2 * (4 * Real.sqrt 2560 + 2560)

/-- All four mixed fibers of the actual reference change, with the full
activation loss and the actual primary pool size. -/
theorem actual_pair_reference_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter) :
    ∀ᶠ parameter in atTop, ∀ (body : FiniteDist (Fin (Parameters.modulus parameter))) (bodyPool radius : ℝ),
      RepresentedPolynomial.inputWeight (actualPrimaryLaw cutoffScale parameter (beta parameter)) body
        (pool parameter : ℝ) bodyPool radius (actualPairReferenceInput cutoffScale parameter (beta parameter)) ≤
      (Real.sqrt (pool parameter : ℝ))⁻¹ ^ 2 * pairReferenceMixedConstant cutoffScale / (parameter : ℝ) ^ 2 := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun _ h => And.intro h.1.1 (And.intro h.1.2 h.2))
  have hprimary := primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel
  filter_upwards [actual_pair_reference_change_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta, hprimary, htypical, eventually_ge_atTop 2]
    with parameter hf hl hp ht hlarge
  intro body bodyPool radius
  rw [actualPairReferenceInput, primaryPairSeed_weight]
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hp1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hp0 : (0 : ℝ) < parameter := zero_lt_one.trans_le hp1
  have hqUpper : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (by simpa only [Parameters.security_eq parameter hlarge] using (Parameters.modulus_bounds parameter).2)
  have hlower (x) : 1 / (4 * (Parameters.modulus parameter : ℝ)) ≤
      (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight x := by
    rw [hl.1]
    exact hp.1 x
  have hrate : (Real.sqrt (pool parameter : ℝ))⁻¹ ≤ 2 / (parameter : ℝ)^15 := by
    simpa only [one_div, Parameters.security_eq parameter hlarge] using (v7_primary_pool_rate_bound parameter (pool parameter) ht.2.2).2
  have ha := v7Activation_square_inverse_upper cutoffScale hscale parameter (by omega)
  have hfull : ((v7Activation cutoffScale parameter ^ 2)⁻¹ *
      ((Parameters.modulus parameter : ℝ) * countingL2 (actualPairReferenceChange cutoffScale parameter (beta parameter))))^2 ≤
      activationConstant cutoffScale ^ 4 * 2560 / (parameter : ℝ)^4 := by
    rw [mul_pow]
    calc
      _ ≤ (activationConstant cutoffScale ^ 2 * (parameter : ℝ)^9)^2 * (2560 / (parameter : ℝ)^38) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) ha 2) hf.1 (sq_nonneg _) (by positivity)
      _ = activationConstant cutoffScale ^ 4 * 2560 / (parameter : ℝ)^20 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hp1 (by decide))
  have hpoint : SupBound (8 * 2 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^32))
      (actualPairReferenceChange cutoffScale parameter (beta parameter)) := by
    intro point
    exact (hf.2.2.2 point).trans (by gcongr; norm_num)
  have hh := activated_pair_residual_activity_le (parameter : ℝ) (Parameters.modulus parameter)
    2 (activationConstant cutoffScale) 2560 (Real.sqrt (pool parameter : ℝ))⁻¹
    hp1 hq (by norm_num) (activationConstant_pos cutoffScale hscale).le (by norm_num) (by positivity) hrate hqUpper
    (actualPrimaryLaw cutoffScale parameter (beta parameter)) hlower _ (v7Activation cutoffScale parameter ^ 2)⁻¹
    (by positivity) ha hfull (by convert hf.2.1 using 1; norm_num) (by convert hf.2.2.1 using 1; norm_num) hpoint
  exact hh.trans_eq (by unfold pairReferenceMixedConstant; ring)

end
end AFT.V7Calibration

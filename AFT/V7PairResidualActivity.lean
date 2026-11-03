import AFT.PairResidualActivity
import AFT.V7ReferenceLaws
import AFT.RepresentedPolynomial

/-! # Actual mixed activity of the literal primary pair residual seed -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology
open SafeConvolution

noncomputable section
attribute [local instance] actualModulusNeZero

def pairResidualMixedConstant (cutoffScale : ℝ) : ℝ :=
  activationConstant cutoffScale ^ 2 *
    (4 * Real.sqrt pairCertificateConstant + 1280 * (pairNeumannConstant + 1))

theorem v7Activation_square_inverse_upper (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (parameter : ℕ) (hp : 1 ≤ parameter) :
    (v7Activation cutoffScale parameter ^ 2)⁻¹ ≤ activationConstant cutoffScale ^ 2 * (parameter : ℝ) ^ 9 := by
  have hp1 : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < parameter := zero_lt_one.trans_le hp1
  have hc := activationConstant_pos cutoffScale hscale
  have hrho : 0 < v7Activation cutoffScale parameter := lt_of_lt_of_le (by positivity)
    (v7Activation_lower_rpow cutoffScale parameter hscale hp)
  have hh := pow_le_pow_left₀ (inv_nonneg.mpr hrho.le) (v7Activation_inverse_upper cutoffScale parameter hscale hp) 2
  rw [mul_pow, inv_pow] at hh
  have hpowers : ((parameter : ℝ) ^ (17/4 : ℝ)) ^ 2 = (parameter : ℝ) ^ (17/2 : ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hp0.le]
    norm_num
  rw [hpowers] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [← Real.rpow_natCast _ 9]
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)

def actualPairResidualInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (mass : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) where
  primaryOrder := 2
  bodyOrder := 0
  kernel := MixedKernel.pairKernel (fun x y =>
    (v7Activation cutoffScale parameter ^ 2)⁻¹ *
      (convolution (actualRootPair parameter).weight
        (actualCompactRootInput parameter 14 (actualPairCoreSeed parameter 14 mass)) -
        uniformCanonical (fun point => mass point.1 point.2)) (x,y) /
      ((V7Calibration.actualPrimaryLaw cutoffScale parameter beta).weight x *
       (V7Calibration.actualPrimaryLaw cutoffScale parameter beta).weight y))

theorem actualPairResidualInput_weight (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (mass : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ)
    (body : FiniteDist (Fin (Parameters.modulus parameter))) (primaryPool bodyPool radius : ℝ) :
    RepresentedPolynomial.inputWeight (V7Calibration.actualPrimaryLaw cutoffScale parameter beta) body
      primaryPool bodyPool radius (actualPairResidualInput cutoffScale parameter beta mass) =
    MixedKernel.activity ![(Real.sqrt primaryPool)⁻¹,(Real.sqrt primaryPool)⁻¹]
      (MixedKernel.pairReference (V7Calibration.actualPrimaryLaw cutoffScale parameter beta)
        (V7Calibration.actualPrimaryLaw cutoffScale parameter beta))
      (actualPairResidualInput cutoffScale parameter beta mass).kernel := by
  have hrate : RepresentedPolynomial.inputRate primaryPool bodyPool (actualPairResidualInput cutoffScale parameter beta mass) =
      ![(Real.sqrt primaryPool)⁻¹,(Real.sqrt primaryPool)⁻¹] := by funext i; fin_cases i <;> rfl
  have href : RepresentedPolynomial.inputReference (V7Calibration.actualPrimaryLaw cutoffScale parameter beta) body
      (actualPairResidualInput cutoffScale parameter beta mass) =
      MixedKernel.pairReference (V7Calibration.actualPrimaryLaw cutoffScale parameter beta)
        (V7Calibration.actualPrimaryLaw cutoffScale parameter beta) := by funext i; fin_cases i <;> rfl
  unfold RepresentedPolynomial.inputWeight MixedKernel.analyticActivity
  rw [hrate, href]
  simp only [actualPairResidualInput, pow_zero, one_mul]
  rfl

/-- This is the actual primary residual seed's literal input weight. It
includes the sharp activation loss and every fixed-coordinate subset. -/
theorem actual_pair_residual_activity_eventually {σ : ℕ → Type*} [∀ parameter, Fintype (σ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter)
    (boundary : ℕ → ℤ) (starts sources : (parameter : ℕ) → σ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (hphysical : ∀ᶠ parameter : ℕ in atTop,
      (0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) ∧
      (∀ sample shift, shift ∈ anchorInterval (starts parameter sample) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
      (∀ sample, |sources parameter sample| ≤ legCutoff cutoffScale parameter)) :
    ∀ᶠ parameter in atTop,
      let mass := TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter)
        (starts parameter) (sources parameter) (sourceLaw parameter).weight (Parameters.anchorWidth parameter)
      ∀ (body : FiniteDist (Fin (Parameters.modulus parameter))) (bodyPool radius : ℝ),
      RepresentedPolynomial.inputWeight (V7Calibration.actualPrimaryLaw cutoffScale parameter (beta parameter)) body
        (pool parameter : ℝ) bodyPool radius (actualPairResidualInput cutoffScale parameter (beta parameter) mass) ≤
      (Real.sqrt (pool parameter : ℝ))⁻¹ ^ 2 * pairResidualMixedConstant cutoffScale / (parameter : ℝ) ^ 2 := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun _ h => And.intro h.1.1 (And.intro h.1.2 h.2))
  have hprimary := V7Calibration.primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel
  filter_upwards [actual_pair_input_fibers_eventually cutoffScale hscale boundary starts sources sourceLaw hphysical,
    actual_pair_certificate_activated_square_eventually cutoffScale hscale boundary starts sources sourceLaw hphysical,
    V7Calibration.actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    hprimary, htypical, eventually_ge_atTop 2] with parameter hf he hl hp ht hlarge
  dsimp only at hf he ⊢
  intro body bodyPool radius
  rw [actualPairResidualInput_weight]
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hqUpper : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (by simpa only [Parameters.security_eq parameter hlarge] using (Parameters.modulus_bounds parameter).2)
  have hlower (x) : 1 / (4 * (Parameters.modulus parameter : ℝ)) ≤
      (V7Calibration.actualPrimaryLaw cutoffScale parameter (beta parameter)).weight x := by
    rw [hl.1]
    exact hp.1 x
  have hrate : (Real.sqrt (pool parameter : ℝ))⁻¹ ≤ 2 / (parameter : ℝ)^15 := by
    simpa only [one_div, Parameters.security_eq parameter hlarge] using (v7_primary_pool_rate_bound parameter (pool parameter) ht.2.2).2
  have hh := activated_pair_residual_activity_le (parameter : ℝ) (Parameters.modulus parameter)
    (pairNeumannConstant+1) (activationConstant cutoffScale) pairCertificateConstant (Real.sqrt (pool parameter : ℝ))⁻¹
    (by exact_mod_cast (by omega : 1 ≤ parameter)) hq (by norm_num [pairNeumannConstant])
    (activationConstant_pos cutoffScale hscale).le (by unfold pairCertificateConstant; positivity) (by positivity) hrate hqUpper
    (V7Calibration.actualPrimaryLaw cutoffScale parameter (beta parameter)) hlower _ (v7Activation cutoffScale parameter ^ 2)⁻¹
    (by positivity) (v7Activation_square_inverse_upper cutoffScale hscale parameter (by omega))
    he hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2
  exact hh.trans_eq (by unfold pairResidualMixedConstant; ring)

end
end AFT.GaussianSource

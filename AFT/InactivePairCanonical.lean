import AFT.InactivePairDifference
import AFT.MixedProducts

/-! # Canonical endpoint source differences as actual finite input seeds -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology
noncomputable section

def inactiveEndpointMarginalDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (source : ℤ)
    (first : Fin (Parameters.modulus parameter)) : ℝ :=
  (∑ second, inactiveEndpointDifference cutoffScale parameter source first second) /
    actualPrimary cutoffScale parameter beta first

def inactiveCanonicalPairDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  SafePair.canonicalPair (actualReferenceMean cutoffScale parameter beta)
    (inactiveEndpointDifference cutoffScale parameter source) first second /
      (actualPrimary cutoffScale parameter beta first * actualPrimary cutoffScale parameter beta second)

def inactiveCanonicalPairInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (source : ℤ) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) where
  primaryOrder := 2
  bodyOrder := 0
  kernel := MixedKernel.pairKernel (inactiveCanonicalPairDensity cutoffScale parameter beta source)

theorem inactiveCanonicalPairDensity_formula (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (source : ℤ)
    (hmass : (∑ first, ∑ second, inactiveEndpointDifference cutoffScale parameter source first second) = 0)
    (first second : Fin (Parameters.modulus parameter)) :
    inactiveCanonicalPairDensity cutoffScale parameter beta source first second =
      inactiveEndpointDensity cutoffScale parameter beta source first second -
        (actualReferenceMean cutoffScale parameter beta first / actualPrimary cutoffScale parameter beta first) *
          inactiveEndpointMarginalDensity cutoffScale parameter beta source second -
        inactiveEndpointMarginalDensity cutoffScale parameter beta source first *
          (actualReferenceMean cutoffScale parameter beta second / actualPrimary cutoffScale parameter beta second) := by
  unfold inactiveCanonicalPairDensity SafePair.canonicalPair inactiveEndpointDensity inactiveEndpointMarginalDensity
  rw [hmass]
  have hs : (∑ x, inactiveEndpointDifference cutoffScale parameter source x second) =
      ∑ x, inactiveEndpointDifference cutoffScale parameter source second x := by
    apply Finset.sum_congr rfl
    intro x _
    exact inactiveEndpointDifference_symmetric cutoffScale parameter source x second
  rw [hs]
  field_simp
  ring

theorem inactiveCanonicalPairInput_weight (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (source : ℤ)
    (primary body : FiniteDist (Fin (Parameters.modulus parameter))) (primaryPool bodyPool radius : ℝ) :
    RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius
      (inactiveCanonicalPairInput cutoffScale parameter beta source) =
      MixedKernel.activity ![(Real.sqrt primaryPool)⁻¹, (Real.sqrt primaryPool)⁻¹]
        (MixedKernel.pairReference primary primary)
        (MixedKernel.pairKernel (inactiveCanonicalPairDensity cutoffScale parameter beta source)) := by
  have hrate : RepresentedPolynomial.inputRate primaryPool bodyPool (inactiveCanonicalPairInput cutoffScale parameter beta source) =
      ![(Real.sqrt primaryPool)⁻¹, (Real.sqrt primaryPool)⁻¹] := by funext i; fin_cases i <;> rfl
  have href : RepresentedPolynomial.inputReference primary body (inactiveCanonicalPairInput cutoffScale parameter beta source) =
      MixedKernel.pairReference primary primary := by funext i; fin_cases i <;> rfl
  unfold RepresentedPolynomial.inputWeight MixedKernel.analyticActivity
  rw [hrate, href]
  simp only [inactiveCanonicalPairInput, pow_zero, one_mul]
  rfl

/-- The actual signed endpoint seed is canonical in both coordinates. -/
theorem actual_inactive_endpoint_canonical_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ source : ℤ,
      (∀ first, ∑ second, SafePair.canonicalPair (actualReferenceMean cutoffScale parameter (beta parameter))
        (inactiveEndpointDifference cutoffScale parameter source) first second = 0) ∧
      (∀ second, ∑ first, SafePair.canonicalPair (actualReferenceMean cutoffScale parameter (beta parameter))
        (inactiveEndpointDifference cutoffScale parameter source) first second = 0) := by
  filter_upwards [actual_reference_probability_eventually cutoffScale hscale beta hbeta] with parameter hr source
  exact ⟨SafePair.canonicalPair_first _ _ hr.2, SafePair.canonicalPair_second _ _ hr.2⟩

/-- Complete primary-pool activity of the actual canonical source pair;
the marginal corrections are charged before root evaluation. -/
theorem actual_inactive_canonical_pair_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ source : Window (legCutoff cutoffScale parameter - 1),
      ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool bodyPool radius : ℝ,
      RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius
        (inactiveCanonicalPairInput cutoffScale parameter (beta parameter) source) ≤
      let a := (Real.sqrt primaryPool)⁻¹
      let F := Real.sqrt (1024 * (Parameters.modulus parameter : ℝ) * legCutoff cutoffScale parameter /
        (Parameters.anchorWidth parameter : ℝ) ^ 2)
      let V := 32 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter
      let G := 16 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
      let Y := 32 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
      a*a*(F + a*F + a*F + a*a*V) + 2*a*a*(3+8*a)*(G+a*Y) := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [actual_inactive_endpoint_density_eventually cutoffScale hscale beta hbeta,
    actual_inactive_endpoint_counting_eventually cutoffScale hscale,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta,
    primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
      (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
      (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel]
    with parameter hd hc hr hp source primary body hprimary primaryPool bodyPool radius
  dsimp only at hd hp ⊢
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  let D := inactiveEndpointDensity cutoffScale parameter (beta parameter) source
  let M := inactiveEndpointMarginalDensity cutoffScale parameter (beta parameter) source
  let R := fun color => r color / p color
  let a := (Real.sqrt primaryPool)⁻¹
  let F := Real.sqrt (1024 * (Parameters.modulus parameter : ℝ) * legCutoff cutoffScale parameter /
    (Parameters.anchorWidth parameter : ℝ)^2)
  let G := 16 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
  let Y := 32 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
  let V := 32 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hp0 (color) : 0 < p color := lt_of_lt_of_le (by positivity) (hp.1 color)
  have ha : 0 ≤ a := by positivity
  have hR (color) : |R color| ≤ 8 := by
    have hh := mul_le_mul_of_nonneg_left (hp.1 color) (by norm_num : (0 : ℝ) ≤ 8)
    have hh' : 2 / (Parameters.modulus parameter : ℝ) ≤ 8 * p color := by convert hh using 1; ring
    rw [abs_of_nonneg (div_nonneg (hr.1 color).1 (hp0 color).le)]
    exact (div_le_iff₀ (hp0 color)).mpr ((hr.1 color).2.trans hh')
  have hR2 : (∑ color, primary.weight color * R color^2) ≤ (3:ℝ)^2 := by
    have hh : (∑ color, primary.weight color * R color^2) ≤ 8 * ∑ color, r color := by
      rw [Finset.mul_sum, hprimary]
      apply Finset.sum_le_sum
      intro color _
      have hmul := mul_le_mul_of_nonneg_right (hR color) (hr.1 color).1
      rw [abs_of_nonneg (div_nonneg (hr.1 color).1 (hp0 color).le)] at hmul
      change p color * (r color / p color)^2 ≤ 8 * r color
      change (r color / p color) * r color ≤ 8 * r color at hmul
      convert hmul using 1
      field_simp [ne_of_gt (hp0 color)]
    rw [hr.2] at hh
    norm_num at hh ⊢
    linarith
  have hM : ∀ color, |M color| ≤ Y := (hd source).2.2.2.2.1
  have hM2 : (∑ color, primary.weight color * M color ^ 2) ≤ G^2 := by
    rw [hprimary]
    have heq : (∑ color, p color * M color^2) = ∑ color,
        (∑ second, inactiveEndpointDifference cutoffScale parameter source color second)^2 / p color := by
      apply Finset.sum_congr rfl
      intro color _
      dsimp only [M, inactiveEndpointMarginalDensity]
      change p color * ((_ / p color)^2) = _
      field_simp
    change (∑ color, p color * M color^2) ≤ _
    rw [heq]
    exact (hd source).2.2.2.2.2.trans_eq (by dsimp only [G]; ring)
  have hF : F^2 = 1024 * (Parameters.modulus parameter : ℝ) * legCutoff cutoffScale parameter /
      (Parameters.anchorWidth parameter : ℝ)^2 := Real.sq_sqrt (by positivity)
  have hfull : (∑ x, ∑ y, primary.weight x * primary.weight y * D x y^2) ≤ F^2 := by
    rw [hprimary, hF]
    apply (hd source).2.1.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ Parameters.modulus parameter by positivity) (show (0 : ℝ) ≤ legCutoff cutoffScale parameter by positivity)]
  have hD := MixedKernel.pair_activity_le primary primary D a a F F F V
    ha ha (by positivity) (by positivity) (by positivity) (by positivity) hfull
    (fun x => by rw [hprimary, hF]; exact (hd source).2.2.1 x)
    (fun y => by rw [hprimary, hF]; exact (hd source).2.2.2.1 y) (hd source).1
  have hRM := MixedKernel.pair_product_activity_le primary primary R M a a 3 8 G Y
    ha ha (by norm_num) (by norm_num) (by positivity) (by positivity) hR2 hR hM2 hM
  have hMR := MixedKernel.pair_product_activity_le primary primary M R a a G Y 3 8
    ha ha (by positivity) (by positivity) (by norm_num) (by norm_num) hM2 hM hR2 hR
  have hformula : MixedKernel.pairKernel (inactiveCanonicalPairDensity cutoffScale parameter (beta parameter) source) =
      MixedKernel.pairKernel D - MixedKernel.pairKernel (fun x y => R x*M y) -
        MixedKernel.pairKernel (fun x y => M x*R y) := by
    funext word
    exact inactiveCanonicalPairDensity_formula cutoffScale parameter (beta parameter) source (hc source).1 (word 0) (word 1)
  have hrate : ∀ i : Fin 2, 0 ≤ ![a,a] i := by intro i; fin_cases i <;> exact ha
  rw [inactiveCanonicalPairInput_weight, hformula]
  have hfirst := MixedKernel.activity_sub_le ![a,a] (MixedKernel.pairReference primary primary)
    (MixedKernel.pairKernel D) (MixedKernel.pairKernel (fun x y => R x*M y)) hrate
  have hsecond := MixedKernel.activity_sub_le ![a,a] (MixedKernel.pairReference primary primary)
    (MixedKernel.pairKernel D - MixedKernel.pairKernel (fun x y => R x*M y))
    (MixedKernel.pairKernel (fun x y => M x*R y)) hrate
  change _ ≤ a*a*(F+a*F+a*F+a*a*V) + 2*a*a*(3+8*a)*(G+a*Y)
  linear_combination hsecond + hfirst + hD + hRM + hMR


end
end AFT.V7Calibration

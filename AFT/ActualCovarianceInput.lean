import AFT.InactivePairCanonical
import AFT.MixedTriple

/-! # Actual same-source covariance inputs of degrees two and three -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology
noncomputable section

def inactivePairActivityBound (cutoffScale : ℝ) (parameter : ℕ) (rate : ℝ) : ℝ :=
  let F := Real.sqrt (1024 * (Parameters.modulus parameter : ℝ) * legCutoff cutoffScale parameter /
    (Parameters.anchorWidth parameter : ℝ)^2)
  let G := 16 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
  let Y := 32 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
  let V := 32 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter
  rate*rate*(F+rate*F+rate*F+rate*rate*V) + 2*rate*rate*(3+8*rate)*(G+rate*Y)

def inactiveBodyActivityBound (cutoffScale : ℝ) (parameter : ℕ) (rate : ℝ) : ℝ :=
  rate*(Real.sqrt (384 * (legCutoff cutoffScale parameter : ℝ) / Parameters.modulus parameter)+16*rate)

def actualInactiveTripleKernel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) :
    (Fin 3 → Fin (Parameters.modulus parameter)) → ℝ :=
  ∑ source, (inactiveLegSource cutoffScale parameter).weight source •
    MixedKernel.tripleProductKernel (inactiveCanonicalPairDensity cutoffScale parameter beta source)
      (inactiveAttachedBodyDensity cutoffScale parameter beta queue source)

def actualInactiveTripleInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) :=
  RepresentedPolynomial.primaryTripleInput (actualInactiveTripleKernel cutoffScale parameter beta queue)

def actualInactiveMarginalBodyKernel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (first attached : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
    inactiveEndpointMarginalDensity cutoffScale parameter beta source first *
    inactiveAttachedBodyDensity cutoffScale parameter beta queue source attached

def actualInactiveMarginalBodyInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) :=
  RepresentedPolynomial.primaryPairInput (actualInactiveMarginalBodyKernel cutoffScale parameter beta queue)

/-- The true inactive residual splits into a canonical cubic coefficient
and its two actual endpoint/body quadratic coefficients. -/
theorem actual_inactive_residual_input_identity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (hzero : ∀ source : Window (legCutoff cutoffScale parameter - 1),
      (∑ first, ∑ second, inactiveEndpointDifference cutoffScale parameter source first second) = 0)
    (first second attached : Fin (Parameters.modulus parameter)) :
    actualInactiveResidual cutoffScale parameter beta queue first second attached /
        (actualPrimary cutoffScale parameter beta first * actualPrimary cutoffScale parameter beta second *
          actualPrimary cutoffScale parameter beta attached) =
      actualInactiveTripleKernel cutoffScale parameter beta queue ![first,second,attached] +
        (actualReferenceMean cutoffScale parameter beta first / actualPrimary cutoffScale parameter beta first) *
          actualInactiveMarginalBodyKernel cutoffScale parameter beta queue second attached +
        actualInactiveMarginalBodyKernel cutoffScale parameter beta queue first attached *
          (actualReferenceMean cutoffScale parameter beta second / actualPrimary cutoffScale parameter beta second) := by
  have ht : Matrix.vecHead (Matrix.vecTail ![second, attached]) = attached := rfl
  simp only [actualInactiveResidual, actualInactiveTripleKernel, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, MixedKernel.tripleProductKernel, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, ht, actualInactiveMarginalBodyKernel, Finset.sum_div,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _
  rw [inactiveCanonicalPairDensity_formula cutoffScale parameter beta source (hzero source)]
  unfold inactiveEndpointDensity inactiveEndpointDifference inactiveEndpointMarginalDensity
    inactiveAttachedBodyDensity inactiveAttachedBodyDifference
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- The complete cubic activity is bounded source by source, then averaged
under the same actual conditional law. -/
theorem actual_inactive_triple_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ queue : ℤ, ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool bodyPool radius : ℝ,
      RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius
        (actualInactiveTripleInput cutoffScale parameter (beta parameter) queue) ≤
      inactivePairActivityBound cutoffScale parameter (Real.sqrt primaryPool)⁻¹ *
        inactiveBodyActivityBound cutoffScale parameter (Real.sqrt primaryPool)⁻¹ := by
  filter_upwards [actual_inactive_canonical_pair_activity_eventually cutoffScale hscale beta hbeta,
    actual_inactive_body_difference_eventually cutoffScale hscale beta hbeta]
    with parameter hpair hbody queue primary body hp primaryPool bodyPool radius
  let a := (Real.sqrt primaryPool)⁻¹
  have ha : 0 ≤ a := by positivity
  letI : Nonempty (Fin (Parameters.modulus parameter)) := ⟨⟨0, (Parameters.modulus_prime parameter).pos⟩⟩
  have hs (source : Window (legCutoff cutoffScale parameter - 1)) :
      MixedKernel.activity (fun _ : Fin 3 => a) (fun _ => primary)
        (MixedKernel.tripleProductKernel (inactiveCanonicalPairDensity cutoffScale parameter (beta parameter) source)
          (inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source)) ≤
        inactivePairActivityBound cutoffScale parameter a * inactiveBodyActivityBound cutoffScale parameter a := by
    have hP := hpair source primary body hp primaryPool bodyPool radius
    rw [inactiveCanonicalPairInput_weight] at hP
    have hB := MixedKernel.singleton_activity_le primary
      (inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source) a
      (Real.sqrt (384*(legCutoff cutoffScale parameter : ℝ)/Parameters.modulus parameter)) 16
      ha (Real.sqrt_nonneg _) (by norm_num)
      (by rw [hp, Real.sq_sqrt (by positivity)]; exact (hbody queue source).2) (hbody queue source).1
    apply (MixedKernel.tripleProduct_activity_le primary _ _ a ha).trans
    have hB' : MixedKernel.activity (fun _ : Fin 1 => a) (fun _ => primary)
        (MixedKernel.singletonKernel (inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source)) ≤
        inactiveBodyActivityBound cutoffScale parameter a := hB.trans_eq (by unfold inactiveBodyActivityBound; ring)
    exact mul_le_mul hP hB'
      (MixedKernel.activity_nonneg _ _ _ (fun _ => ha)) (by unfold inactivePairActivityBound; positivity)
  rw [actualInactiveTripleInput, RepresentedPolynomial.primaryTripleInput_weight]
  apply (MixedKernel.activity_average_le (fun _ : Fin 3 => a) (fun _ => primary) _
    (inactiveLegSource cutoffScale parameter) (fun _ => ha)).trans
  calc
    _ ≤ ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
        (inactivePairActivityBound cutoffScale parameter a * inactiveBodyActivityBound cutoffScale parameter a) :=
      Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left (hs source) (FiniteDist.nonneg _ source)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

/-- The two quadratic coefficients use the actual endpoint marginal
differences and retain the complete fixed-body fiber. -/
theorem actual_inactive_marginal_body_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ queue : ℤ, ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool bodyPool radius : ℝ,
      RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius
        (actualInactiveMarginalBodyInput cutoffScale parameter (beta parameter) queue) ≤
      let a := (Real.sqrt primaryPool)⁻¹
      let G := 16 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
      let Y := 32 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
      a * (G+a*Y) * inactiveBodyActivityBound cutoffScale parameter a := by
  filter_upwards [actual_inactive_endpoint_density_eventually cutoffScale hscale beta hbeta,
    actual_inactive_body_difference_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta]
    with parameter hpair hbody hpositive queue primary body hp primaryPool bodyPool radius
  dsimp only
  let a := (Real.sqrt primaryPool)⁻¹
  let G := 16 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
  let Y := 32 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter
  let H := Real.sqrt (384 * (legCutoff cutoffScale parameter : ℝ) / Parameters.modulus parameter)
  have ha : 0 ≤ a := by positivity
  have hs (source : Window (legCutoff cutoffScale parameter - 1)) :
      MixedKernel.activity ![a,a] (MixedKernel.pairReference primary primary)
        (MixedKernel.pairKernel (fun first attached => inactiveEndpointMarginalDensity cutoffScale parameter (beta parameter) source first *
          inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source attached)) ≤
        a*(G+a*Y)*inactiveBodyActivityBound cutoffScale parameter a := by
    have hm : (∑ color, primary.weight color *
        inactiveEndpointMarginalDensity cutoffScale parameter (beta parameter) source color ^ 2) ≤ G^2 := by
      rw [hp]
      have heq : (∑ color, actualPrimary cutoffScale parameter (beta parameter) color *
          inactiveEndpointMarginalDensity cutoffScale parameter (beta parameter) source color ^ 2) =
          ∑ color, (∑ second, inactiveEndpointDifference cutoffScale parameter source color second)^2 /
            actualPrimary cutoffScale parameter (beta parameter) color := by
        apply Finset.sum_congr rfl
        intro color _
        unfold inactiveEndpointMarginalDensity
        field_simp
      rw [heq]
      exact (hpair source).2.2.2.2.2.trans_eq (by dsimp only [G]; ring)
    have hh := MixedKernel.pair_product_activity_le primary primary
      (inactiveEndpointMarginalDensity cutoffScale parameter (beta parameter) source)
      (inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source)
      a a G Y H 16 ha ha (by positivity) (by positivity) (by positivity) (by norm_num)
      hm (hpair source).2.2.2.2.1
      (by rw [hp]; dsimp only [H]; rw [Real.sq_sqrt (by positivity)]; exact (hbody queue source).2)
      (hbody queue source).1
    exact hh.trans_eq (by dsimp only [H, inactiveBodyActivityBound]; ring)
  have heq : MixedKernel.pairKernel (actualInactiveMarginalBodyKernel cutoffScale parameter (beta parameter) queue) =
      ∑ source, (inactiveLegSource cutoffScale parameter).weight source •
        MixedKernel.pairKernel (fun first attached => inactiveEndpointMarginalDensity cutoffScale parameter (beta parameter) source first *
          inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source attached) := by
    funext word
    simp only [MixedKernel.pairKernel, actualInactiveMarginalBodyKernel, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [actualInactiveMarginalBodyInput, RepresentedPolynomial.primaryPairInput_weight, heq]
  have hrate : ∀ i : Fin 2, 0 ≤ ![a,a] i := by intro i; fin_cases i <;> exact ha
  apply (MixedKernel.activity_average_le ![a,a] (MixedKernel.pairReference primary primary) _
    (inactiveLegSource cutoffScale parameter) hrate).trans
  calc
    _ ≤ ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
        (a*(G+a*Y)*inactiveBodyActivityBound cutoffScale parameter a) :=
      Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left (hs source) (FiniteDist.nonneg _ source)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

end
end AFT.V7Calibration

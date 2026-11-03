import AFT.ActiveCanonicalInput
import AFT.MixedCanonical

/-! # Actual weighted canonicality of every attachment covariance input -/

namespace AFT.V7Calibration
open Filter GaussianSource
open scoped BigOperators Classical Topology
noncomputable section

theorem actual_covariance_inputs_canonical_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ queue : ℤ, |queue| ≤ queueCutoff parameter →
      ∀ primary : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      Hoeffding.Canonical (fun _ : Fin 3 => primary) Finset.univ
        (actualInactiveTripleInput cutoffScale parameter (beta parameter) queue).kernel ∧
      Hoeffding.Canonical (fun _ : Fin 2 => primary) Finset.univ
        (actualInactiveMarginalBodyInput cutoffScale parameter (beta parameter) queue).kernel ∧
      Hoeffding.Canonical (fun _ : Fin 3 => primary) Finset.univ
        (actualActiveTripleInput cutoffScale parameter (beta parameter) queue).kernel ∧
      (∀ side : Bool, Hoeffding.Canonical (fun _ : Fin 2 => primary) Finset.univ
        (actualActiveMarginalBodyInput cutoffScale parameter (beta parameter) queue side).kernel) := by
  filter_upwards [actual_inactive_body_canonical_eventually cutoffScale hscale beta hbeta,
    actual_inactive_endpoint_counting_eventually cutoffScale hscale,
    actual_active_endpoint_density_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta]
    with parameter hbody hcounts hactive hp hr queue hqueue primary hprimary
  dsimp only at hactive
  have hp0 (color) : 0 < primary.weight color := by rw [hprimary]; exact hp.1 color
  have hb (source : Window (legCutoff cutoffScale parameter - 1)) :
      (∑ color, primary.weight color * inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source color) = 0 := by
    calc
      _ = ∑ color, inactiveAttachedBodyDifference cutoffScale parameter (beta parameter) queue source color := by
        apply Finset.sum_congr rfl
        intro color _
        rw [hprimary]
        unfold inactiveAttachedBodyDensity
        field_simp [ne_of_gt (hp.1 color)]
      _ = 0 := hbody queue hqueue source
  have hpair (source : Window (legCutoff cutoffScale parameter - 1)) :
      Hoeffding.Canonical (fun _ : Fin 2 => primary) Finset.univ
        (MixedKernel.pairKernel (inactiveCanonicalPairDensity cutoffScale parameter (beta parameter) source)) := by
    simpa only [hprimary, inactiveCanonicalPairDensity] using
      MixedKernel.canonicalPair_density_canonical primary (actualReferenceMean cutoffScale parameter (beta parameter))
        (inactiveEndpointDifference cutoffScale parameter source) hp0 hr.2
  have hm (source : Window (legCutoff cutoffScale parameter - 1)) :
      (∑ color, primary.weight color * inactiveEndpointMarginalDensity cutoffScale parameter (beta parameter) source color) = 0 := by
    calc
      _ = ∑ color, ∑ other, inactiveEndpointDifference cutoffScale parameter source color other := by
        apply Finset.sum_congr rfl
        intro color _
        rw [hprimary]
        unfold inactiveEndpointMarginalDensity
        field_simp [ne_of_gt (hp.1 color)]
      _ = 0 := (hcounts source).1
  have hb0 : (∑ color, primary.weight color * inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue 0 color) = 0 :=
    hb (windowZero (legCutoff cutoffScale parameter - 1))
  have hactivePair : Hoeffding.Canonical (fun _ : Fin 2 => primary) Finset.univ
      (MixedKernel.pairKernel (activeCanonicalPairDensity cutoffScale parameter (beta parameter))) := by
    simpa only [hprimary, activeCanonicalPairDensity] using
      MixedKernel.canonicalPair_density_canonical primary (actualReferenceMean cutoffScale parameter (beta parameter))
        (activeEndpointDifference cutoffScale parameter (beta parameter)) hp0 hr.2
  have hactiveMarginal (side : Bool) :
      (∑ color, primary.weight color * activeEndpointMarginalDensity cutoffScale parameter (beta parameter) side color) = 0 := by
    have heq : (∑ color, primary.weight color * activeEndpointMarginalDensity cutoffScale parameter (beta parameter) side color) =
        ∑ color, ∑ other, if side then activeEndpointDifference cutoffScale parameter (beta parameter) color other
          else activeEndpointDifference cutoffScale parameter (beta parameter) other color := by
      apply Finset.sum_congr rfl
      intro color _
      rw [hprimary]
      unfold activeEndpointMarginalDensity
      field_simp [ne_of_gt (hp.1 color)]
    rw [heq]
    cases side
    · simp only [Bool.false_eq_true, if_false]
      rw [Finset.sum_comm]
      exact hactive.1
    · simpa only [if_true] using hactive.1
  refine ⟨?_,?_,?_,?_⟩
  · exact MixedKernel.canonical_average (fun _ : Fin 3 => primary) _ (inactiveLegSource cutoffScale parameter)
      (fun source => MixedKernel.tripleProduct_canonical_of_pair primary _ _ (hpair source) (hb source))
  · have heq : (actualInactiveMarginalBodyInput cutoffScale parameter (beta parameter) queue).kernel =
        ∑ source, (inactiveLegSource cutoffScale parameter).weight source •
          MixedKernel.pairKernel (fun first attached => inactiveEndpointMarginalDensity cutoffScale parameter (beta parameter) source first *
            inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source attached) := by
      funext word
      simp only [actualInactiveMarginalBodyInput, RepresentedPolynomial.primaryPairInput,
        MixedKernel.pairKernel, actualInactiveMarginalBodyKernel, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [heq]
    exact MixedKernel.canonical_average (fun _ : Fin 2 => primary) _ (inactiveLegSource cutoffScale parameter)
      (fun source => MixedKernel.pair_product_canonical primary _ _ (hm source) (hb source))
  · exact MixedKernel.tripleProduct_canonical_of_pair primary _ _ hactivePair hb0
  · intro side
    exact MixedKernel.pair_product_canonical primary _ _ (hactiveMarginal side) hb0

end
end AFT.V7Calibration

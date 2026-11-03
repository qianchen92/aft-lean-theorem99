import AFT.PhysicalCovarianceForms

/-! # Actual covariance tables equal the full physical covariance generating law -/
namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def inactiveCanonicalTripleMass (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (first second attached : Fin (Parameters.modulus n)) : ℝ :=
  ∑ source, (inactiveLegSource C n).weight source *
    SafePair.canonicalPair (actualReferenceMean C n beta) (inactiveEndpointDifference C n source) first second *
    inactiveAttachedBodyDifference C n beta queue source attached

def inactiveMarginalBodyMass (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (first attached : Fin (Parameters.modulus n)) : ℝ :=
  ∑ source, (inactiveLegSource C n).weight source * (∑ other, inactiveEndpointDifference C n source first other) *
    inactiveAttachedBodyDifference C n beta queue source attached

def activeCanonicalTripleMass (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (first second attached : Fin (Parameters.modulus n)) : ℝ :=
  SafePair.canonicalPair (actualReferenceMean C n beta) (activeEndpointDifference C n beta) first second *
    inactiveAttachedBodyDifference C n beta queue 0 attached

def activeMarginalBodyMass (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ) (side : Bool)
    (first attached : Fin (Parameters.modulus n)) : ℝ :=
  (∑ other, if side then activeEndpointDifference C n beta first other else activeEndpointDifference C n beta other first) *
    inactiveAttachedBodyDifference C n beta queue 0 attached

theorem inactive_triple_primary_form (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (hprimary : (actualPrimaryLaw C n beta).weight = actualPrimary C n beta)
    (hp : ∀ color, actualPrimary C n beta color ≠ 0) :
    jointPrimaryForm (actualPrimaryLaw C n beta) (actualInactiveTripleInput C n beta queue) =
      tripleForm (inactiveCanonicalTripleMass C n beta queue) := by
  rw [actualInactiveTripleInput, jointPrimaryForm_triple]
  apply congrArg tripleForm
  funext first second third
  rw [hprimary]
  exact inactive_triple_weighted_mass C n beta queue hp ![first, second, third]

theorem inactive_pair_primary_form (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (hprimary : (actualPrimaryLaw C n beta).weight = actualPrimary C n beta)
    (hp : ∀ color, actualPrimary C n beta color ≠ 0) :
    jointPrimaryForm (actualPrimaryLaw C n beta) (actualInactiveMarginalBodyInput C n beta queue) =
      pairForm (inactiveMarginalBodyMass C n beta queue) := by
  rw [actualInactiveMarginalBodyInput, jointPrimaryForm_pair]
  apply congrArg pairForm
  funext first second
  rw [hprimary]
  exact inactive_pair_weighted_mass C n beta queue hp first second

theorem active_triple_primary_form (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (hprimary : (actualPrimaryLaw C n beta).weight = actualPrimary C n beta)
    (hp : ∀ color, actualPrimary C n beta color ≠ 0) :
    jointPrimaryForm (actualPrimaryLaw C n beta) (actualActiveTripleInput C n beta queue) =
      tripleForm (activeCanonicalTripleMass C n beta queue) := by
  rw [actualActiveTripleInput, jointPrimaryForm_triple]
  apply congrArg tripleForm
  funext first second third
  rw [hprimary]
  exact active_triple_weighted_mass C n beta queue hp ![first, second, third]

theorem active_pair_primary_form (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ) (side : Bool)
    (hprimary : (actualPrimaryLaw C n beta).weight = actualPrimary C n beta)
    (hp : ∀ color, actualPrimary C n beta color ≠ 0) :
    jointPrimaryForm (actualPrimaryLaw C n beta) (actualActiveMarginalBodyInput C n beta queue side) =
      pairForm (activeMarginalBodyMass C n beta queue side) := by
  rw [actualActiveMarginalBodyInput, jointPrimaryForm_pair]
  apply congrArg pairForm
  funext first second
  rw [hprimary]
  exact active_pair_weighted_mass C n beta queue hp side first second

/-- The symmetric inactive endpoint law has two identical, genuine
endpoint/body quadratic companions. -/
theorem inactive_residual_generating (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (hpair : ∀ source : Window (legCutoff C n - 1), (∑ a, ∑ b, inactiveEndpointDifference C n source a b) = 0)
    (hbody : ∀ source : Window (legCutoff C n - 1), (∑ c, inactiveAttachedBodyDifference C n beta queue source c) = 0) :
    tripleGenerating (actualReferenceMean C n beta) (actualInactiveResidual C n beta queue) =
      tripleForm (inactiveCanonicalTripleMass C n beta queue) + 2 * pairForm (inactiveMarginalBodyMass C n beta queue) := by
  have hh := tripleGenerating_source_covariance (actualReferenceMean C n beta) (inactiveLegSource C n).weight
    (fun source => inactiveEndpointDifference C n source) (fun source => inactiveAttachedBodyDifference C n beta queue source) hpair hbody
  have hc : (fun b c => ∑ source, (inactiveLegSource C n).weight source *
      (∑ a, inactiveEndpointDifference C n source a b) * inactiveAttachedBodyDifference C n beta queue source c) =
      inactiveMarginalBodyMass C n beta queue := by
    funext b c
    unfold inactiveMarginalBodyMass
    simp only [inactiveEndpointDifference_symmetric C n _ _ b]
  rw [hc] at hh
  change tripleGenerating (actualReferenceMean C n beta) (actualInactiveResidual C n beta queue) =
    tripleForm (inactiveCanonicalTripleMass C n beta queue) + pairForm (inactiveMarginalBodyMass C n beta queue) + pairForm (inactiveMarginalBodyMass C n beta queue) at hh
  rw [hh]
  ring

/-- The complete leading polynomial of the actual inverse covariance table
is precisely the physical local triple minus the product of its actual
pair and body marginals, including its quadratic terms. -/
theorem actual_physical_covariance_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (actualCovarianceTable C n (beta n) queue)) =
      tripleGenerating (actualReferenceMean C n (beta n))
        (fun first second attached => actualLocalTriple C n (beta n) queue first second attached -
          localPairMixture C n (beta n) first second * localBodyMixture C n (beta n) queue attached) := by
  filter_upwards [actual_covariance_output_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,
    actual_inactive_endpoint_counting_eventually C hC,
    actual_inactive_body_canonical_eventually C hC beta hbeta,
    actual_active_endpoint_density_eventually C hC beta hbeta]
    with n hout hl hp hi hb ha operator hop queue hqueue
  have hp0 (color) : actualPrimary C n (beta n) color ≠ 0 := (hp.1 color).ne'
  have hI := inactive_residual_generating C n (beta n) queue (fun source => (hi source).1) (hb queue hqueue)
  have hA := tripleGenerating_covariance (actualReferenceMean C n (beta n)) (activeEndpointDifference C n (beta n))
    (inactiveAttachedBodyDifference C n (beta n) queue 0) ha.1 (hb queue hqueue (windowZero (legCutoff C n - 1)))
  change tripleGenerating (actualReferenceMean C n (beta n))
    (fun a b c => activeEndpointDifference C n (beta n) a b * inactiveAttachedBodyDifference C n (beta n) queue 0 c) =
      tripleForm (activeCanonicalTripleMass C n (beta n) queue) +
        pairForm (activeMarginalBodyMass C n (beta n) queue true) + pairForm (activeMarginalBodyMass C n (beta n) queue false) at hA
  have hm : (fun first second attached => actualLocalTriple C n (beta n) queue first second attached -
      localPairMixture C n (beta n) first second * localBodyMixture C n (beta n) queue attached) =
      (1 - v7Activation C n) • actualInactiveResidual C n (beta n) queue +
      (v7Activation C n * (1 - v7Activation C n)) •
        (fun a b c => activeEndpointDifference C n (beta n) a b * inactiveAttachedBodyDifference C n (beta n) queue 0 c) := by
    funext first second attached
    rw [actual_local_triple_decomposition]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, activeEndpointDifference, inactiveAttachedBodyDifference, Pi.sub_apply]
    ring
  rw [hout operator hop queue]
  change _ = covarianceTripleGeneratingLinear (actualReferenceMean C n (beta n)) _
  rw [hm, map_add, map_smul, map_smul]
  change _ = (1 - v7Activation C n) • tripleGenerating (actualReferenceMean C n (beta n)) (actualInactiveResidual C n (beta n) queue) +
    (v7Activation C n * (1 - v7Activation C n)) • tripleGenerating (actualReferenceMean C n (beta n)) _
  rw [hI, hA]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, covarianceCoefficient, actualCovarianceSeed,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  rw [inactive_triple_primary_form C n (beta n) queue hl.1 hp0,
    inactive_pair_primary_form C n (beta n) queue hl.1 hp0,
    active_triple_primary_form C n (beta n) queue hl.1 hp0,
    active_pair_primary_form C n (beta n) queue false hl.1 hp0,
    active_pair_primary_form C n (beta n) queue true hl.1 hp0]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_sub, map_one, map_ofNat]
  ring

end
end AFT.V7Calibration

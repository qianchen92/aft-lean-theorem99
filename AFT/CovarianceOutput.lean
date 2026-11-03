import AFT.JointSeedOutput
import AFT.RepresentedCovariance

/-! # Exact leading images of the actual shared-source covariance seeds -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def jointPrimaryForm (primary : FiniteDist Color) (seed : InputSeed Color) : MvPolynomial Color ℝ :=
  ∑ word : Fin (seed.primaryOrder+seed.bodyOrder) → Color,
    MvPolynomial.C (seed.kernel word*∏ slot,primary.weight (word slot))*∏ slot,MvPolynomial.X (word slot)

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- No primary inverse or activation factor remains in the output of any
of the five actual covariance seeds. Their full joint kernels are preserved. -/
theorem actual_covariance_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ queue,
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (actualCovarianceTable C n (beta n) queue)) =
      ∑ index : Fin 5, MvPolynomial.C (covarianceCoefficient (v7Activation C n) index)*
        jointPrimaryForm (actualPrimaryLaw C n (beta n)) (actualCovarianceSeed C n (beta n) queue index) := by
  filter_upwards [actual_reference_laws_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n hl hp hn operator hop queue
  have hp0 (color) : (actualPrimaryLaw C n (beta n)).weight color ≠ 0 := by rw [hl.1]; exact (hp.1 _).ne'
  have hrho : v7Activation C n ≠ 0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).ne'
  let T := inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (v7Activation C n) operator
  let L := actualLeadingOutput C n (beta n)
  have hC (x : ℝ) : L (T (MvPolynomial.C x)) = MvPolynomial.C x := by
    change L (T (algebraMap ℝ _ x)) = algebraMap ℝ _ x
    rw [T.commutes,L.commutes]
  change L (T _) = _
  simp only [actualCovarianceTable,map_sum,map_mul,hC]
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  dsimp only [L,T,inversePrimaryTable]
  rw [MvPolynomial.aeval_X]
  apply actualLeadingOutput_inverse_joint_primary C n (beta n) operator hop hrho hp0
  fin_cases index <;> rfl

/-- The inactive cubic is the actual finite source average of the canonical
endpoint difference times its own attached-body difference. -/
theorem inactive_triple_weighted_mass (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (hp : ∀ color, actualPrimary C n beta color ≠ 0) (word : Fin 3 → Fin (Parameters.modulus n)) :
    actualInactiveTripleKernel C n beta queue word*
      (actualPrimary C n beta (word 0)*actualPrimary C n beta (word 1)*actualPrimary C n beta (word 2)) =
    ∑ source, (inactiveLegSource C n).weight source*
      SafePair.canonicalPair (actualReferenceMean C n beta) (inactiveEndpointDifference C n source) (word 0) (word 1)*
      inactiveAttachedBodyDifference C n beta queue source (word 2) := by
  simp only [actualInactiveTripleKernel,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul,
    MixedKernel.tripleProductKernel,inactiveCanonicalPairDensity,inactiveAttachedBodyDensity]
  apply Finset.sum_congr rfl
  intro source _
  field_simp [hp]

/-- The actual quadratic companion uses the complete endpoint marginal,
with the identical conditional source as its attached body. -/
theorem inactive_pair_weighted_mass (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (hp : ∀ color, actualPrimary C n beta color ≠ 0) (first attached : Fin (Parameters.modulus n)) :
    actualInactiveMarginalBodyKernel C n beta queue first attached*
      (actualPrimary C n beta first*actualPrimary C n beta attached) =
    ∑ source, (inactiveLegSource C n).weight source*
      (∑ other,inactiveEndpointDifference C n source first other)*
      inactiveAttachedBodyDifference C n beta queue source attached := by
  simp only [actualInactiveMarginalBodyKernel,Finset.sum_mul,inactiveEndpointMarginalDensity,inactiveAttachedBodyDensity]
  apply Finset.sum_congr rfl
  intro source _
  field_simp [hp]

theorem active_triple_weighted_mass (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (hp : ∀ color, actualPrimary C n beta color ≠ 0) (word : Fin 3 → Fin (Parameters.modulus n)) :
    actualActiveTripleKernel C n beta queue word*
      (actualPrimary C n beta (word 0)*actualPrimary C n beta (word 1)*actualPrimary C n beta (word 2)) =
      SafePair.canonicalPair (actualReferenceMean C n beta) (activeEndpointDifference C n beta) (word 0) (word 1)*
      inactiveAttachedBodyDifference C n beta queue 0 (word 2) := by
  simp only [actualActiveTripleKernel,MixedKernel.tripleProductKernel,activeCanonicalPairDensity,inactiveAttachedBodyDensity]
  field_simp [hp]

theorem active_pair_weighted_mass (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (hp : ∀ color, actualPrimary C n beta color ≠ 0) (side : Bool) (first attached : Fin (Parameters.modulus n)) :
    actualActiveMarginalBodyKernel C n beta queue side first attached*
      (actualPrimary C n beta first*actualPrimary C n beta attached) =
      (∑ other,if side then activeEndpointDifference C n beta first other else activeEndpointDifference C n beta other first)*
      inactiveAttachedBodyDifference C n beta queue 0 attached := by
  simp only [actualActiveMarginalBodyKernel,activeEndpointMarginalDensity,inactiveAttachedBodyDensity]
  field_simp [hp]

end
end AFT.V7Calibration

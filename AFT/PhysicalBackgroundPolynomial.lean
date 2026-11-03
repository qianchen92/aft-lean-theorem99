import AFT.EndpointPolynomial
import AFT.PhysicalCovarianceOutput
import AFT.GlobalBackgroundCanonical

/-! # Literal background certificates and the actual physical generating law -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Source Target : Type*}

theorem map_exponential (hom : Table Source →ₐ[ℝ] Table Target) (table : Table Source) (cutoff : ℕ) :
    hom (exponential table cutoff) = exponential (hom table) cutoff := by
  unfold exponential
  simp only [map_sum,map_mul,map_pow]
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  exact hom.commutes _

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance physicalBackgroundPolynomialFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance physicalBackgroundPolynomialSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def blockPhysicalPolynomial (C : ℝ) (n : ℕ) (beta : ℝ) (index : blockIndex n) (queue : ℤ) :
    MvPolynomial (Fin (Parameters.modulus n)) ℝ :=
  match index with
  | .inl _ => tripleGenerating (actualReferenceMean C n beta) (actualLocalTriple C n beta queue)
  | .inr _ => singleGenerating (actualReferenceMean C n beta) (attachedBodyAtSource C n beta queue 0)

theorem actual_attached_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      actualLeadingOutput C n (beta n) (1+localAttachedMeanInputTable C n (beta n) queue operator) =
      singleGenerating (actualReferenceMean C n (beta n)) (localBodyMixture C n (beta n) queue) := by
  filter_upwards [actual_attached_mean_table_output_eventually C hC beta hbeta,
    actual_local_body_mass_eventually C hC beta hbeta] with n ho hm operator hop queue hq
  rw [map_add,map_one]
  dsimp only [localAttachedMeanInputTable]
  rw [ho operator hop queue hq,singleGenerating_mass_one _ _ (hm queue hq)]

theorem actual_local_background_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      actualLeadingOutput C n (beta n) (1+localBackgroundError C n (beta n) queue operator) =
      tripleGenerating (actualReferenceMean C n (beta n)) (actualLocalTriple C n (beta n) queue) := by
  filter_upwards [actual_endpoint_polynomial_eventually C hC beta hbeta,
    actual_attached_polynomial_eventually C hC beta hbeta,
    actual_physical_covariance_output_eventually C hC beta hbeta] with n he hb hc operator hop queue hq
  rw [localBackgroundError_factorization,map_add,map_mul,he operator hop,hb operator hop queue hq]
  dsimp only [localCovarianceInputTable]
  rw [hc operator hop queue hq]
  have hsub : tripleGenerating (actualReferenceMean C n (beta n))
      (fun first second attached => actualLocalTriple C n (beta n) queue first second attached-
        localPairMixture C n (beta n) first second*localBodyMixture C n (beta n) queue attached) =
      tripleGenerating (actualReferenceMean C n (beta n)) (actualLocalTriple C n (beta n) queue)-
      tripleGenerating (actualReferenceMean C n (beta n))
        (fun first second attached => localPairMixture C n (beta n) first second*localBodyMixture C n (beta n) queue attached) :=
    by
      exact (covarianceTripleGeneratingLinear (actualReferenceMean C n (beta n))).map_sub
        (actualLocalTriple C n (beta n) queue)
        (fun first second attached => localPairMixture C n (beta n) first second*localBodyMixture C n (beta n) queue attached)
  rw [hsub,tripleGenerating_tensor]
  ring

theorem actual_block_background_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ index : blockIndex n, ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      actualLeadingOutput C n (beta n) (1+blockBackgroundError C n (beta n) operator index queue) =
      blockPhysicalPolynomial C n (beta n) index queue := by
  filter_upwards [actual_local_background_polynomial_eventually C hC beta hbeta,
    actual_block_body_mean_output_eventually C hC beta hbeta,
    actual_block_body_mass_eventually C hC beta hbeta] with n hl hb hm operator hop index queue hq
  cases index with
  | inl _ => exact hl operator hop queue hq
  | inr body =>
    change _ = singleGenerating (actualReferenceMean C n (beta n))
      (blockBodyMeanProfile C n (beta n) (.inr body) queue)
    rw [singleGenerating_mass_one _ _ (hm (.inr body) queue hq),map_add,map_one]
    exact congrArg (fun value => 1+value) (hb operator hop (.inr body) queue hq)

/-- The actual small, canonical finite log certificate recovers the complete
product of physical block generating polynomials through every fixed cutoff.
Every block uses the same queue sample throughout this identity. -/
theorem actual_background_exponential_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ sample cutoff,
      truncate (fun _ => 1) cutoff (actualLeadingOutput C n (beta n)
        (exponential (actualBackgroundLog C n (beta n) operator sample cutoff) cutoff)) =
      truncate (fun _ => 1) cutoff (∏ index,blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n sample index)) := by
  filter_upwards [actual_background_log_output_eventually C hC beta hbeta,
    actual_block_background_polynomial_eventually C hC beta hbeta] with n hg hb operator hop sample cutoff
  rw [map_exponential,hg operator hop sample cutoff,← map_exponential]
  have ht := outputHom_truncation_respects (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (actualPrimaryChannel C n) (actualBodyChannel n) cutoff _ _
    (truncate_background_exponential (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
      (fun index => blockBackgroundError C n (beta n) operator index (actualQueueShifts n sample index)) Finset.univ
      (fun index _ => blockBackgroundError_hasOrder C n (beta n) operator index _))
  change truncate (fun _ => 1) cutoff (actualLeadingOutput C n (beta n) _) =
    truncate (fun _ => 1) cutoff (actualLeadingOutput C n (beta n) _) at ht
  rw [ht,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  exact hb operator hop index _ (actualQueueShifts_bound n sample index)

end
end AFT.V7Calibration

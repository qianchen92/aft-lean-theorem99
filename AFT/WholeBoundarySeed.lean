import AFT.PrimaryMonomialSeed
import AFT.BoundaryPrimaryTable
import AFT.ActualJointBoundaryActivity

/-! # One whole legal projection on each complete primary monomial -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color] [DecidableEq Color]

def wholeBoundarySeed (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (seed : InputSeed Color) : InputSeed Color where
  primaryOrder := seed.primaryOrder
  bodyOrder := seed.bodyOrder
  kernel := MixedKernel.jointLegalProjection (primaryCoordinates seed).reverse
    (fun _ => legalInputProjection operator (boundaryIdealProjection interior primary.weight))
    (inputReference primary body seed) seed.kernel

theorem wholeBoundarySeed_kernel (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (hrange : ∀ profile,operator profile-profile∈canonicalInteriorProfiles interior)
    (seed : InputSeed Color) (word : Fin (seed.primaryOrder+seed.bodyOrder) → Color) :
    (wholeBoundarySeed primary body operator interior seed).kernel word=
      seed.kernel word-(boundaryPrimarySeed primary body operator interior primary.weight seed).kernel word := by
  unfold wholeBoundarySeed MixedKernel.jointLegalProjection boundaryPrimarySeed
  simp only [legalInputProjection_complement interior primary.weight operator hrange,
    LinearMap.sub_apply,LinearMap.id_apply,Pi.sub_apply]

theorem wholeBoundarySeed_output (primary body : FiniteDist Color)
    (rho : ℝ) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (bodyChannel : Color → Color → ℝ)
    (interior : Finset Color) (hrange : ∀ profile,operator profile-profile∈canonicalInteriorProfiles interior)
    (hprimary : ∀ color,primary.weight color≠0) (seed : InputSeed Color) (hbody : seed.bodyOrder=0) :
    seedOutput primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel
      (wholeBoundarySeed primary body operator interior seed)=
      seedOutput primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel seed-
      boundaryPolynomial interior primary.weight
        (seedOutput primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel seed) := by
  rw [← boundaryPrimarySeed_output primary body rho operator bodyChannel interior primary.weight hrange hprimary seed hbody]
  unfold seedOutput
  have href : inputReference primary body (wholeBoundarySeed primary body operator interior seed)=inputReference primary body seed := rfl
  have hrefb : inputReference primary body (boundaryPrimarySeed primary body operator interior primary.weight seed)=inputReference primary body seed := rfl
  simp only [href,hrefb,wholeBoundarySeed_kernel primary body operator interior hrange seed,
    sub_mul,map_sub,Finset.sum_sub_distrib]
  rfl

theorem wholeBoundarySeed_canonical (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (hprimary : ∀ color,primary.weight color≠0)
    (hlegal : ∀ profile,(∑ color,legalInputProjection operator (boundaryIdealProjection interior primary.weight) profile color)=0)
    (seed : InputSeed Color) (hbody : seed.bodyOrder=0)
    (hc : Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (inputReference primary body (wholeBoundarySeed primary body operator interior seed))
      Finset.univ (wholeBoundarySeed primary body operator interior seed).kernel := by
  change Hoeffding.Canonical (inputReference primary body seed) Finset.univ
    (MixedKernel.jointLegalProjection (primaryCoordinates seed).reverse
      (fun _ => legalInputProjection operator (boundaryIdealProjection interior primary.weight))
      (inputReference primary body seed) seed.kernel)
  apply MixedKernel.jointLegalProjection_canonical
  · intro slot color
    rw [all_primary_reference primary body seed hbody slot]
    exact hprimary color
  · exact fun _ profile => hlegal profile
  · exact hc

theorem wholeBoundarySeed_activity_le (primary body : FiniteDist Color)
    (primaryPool bodyPool radius : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (seed : InputSeed Color) (hbody : seed.bodyOrder=0)
    (hprojection : ∀ kernel,
      MixedKernel.activity (inputRate primaryPool bodyPool seed) (inputReference primary body seed)
        (MixedKernel.jointLegalProjection (primaryCoordinates seed).reverse
          (fun _ => legalInputProjection operator (boundaryIdealProjection interior primary.weight))
          (inputReference primary body seed) kernel)≤
      (1+(8 : ℝ)^seed.primaryOrder)*MixedKernel.activity (inputRate primaryPool bodyPool seed)
        (inputReference primary body seed) kernel) :
    inputWeight primary body primaryPool bodyPool radius (wholeBoundarySeed primary body operator interior seed)≤
      (1+(8 : ℝ)^seed.primaryOrder)*inputWeight primary body primaryPool bodyPool radius seed := by
  simpa only [inputWeight,MixedKernel.analyticActivity,wholeBoundarySeed,hbody,pow_zero,one_mul] using hprojection seed.kernel

end
end AFT.RepresentedPolynomial

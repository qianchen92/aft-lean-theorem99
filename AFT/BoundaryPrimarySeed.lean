import AFT.ProfileTensorBoundary
import AFT.ActualBoundaryComplement
import AFT.JointSeedOutput

/-! # Literal joint primary seeds for the boundary reference transform -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color] [DecidableEq Color]

def boundaryPrimarySeed (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (target : Color → ℝ) (seed : InputSeed Color) : InputSeed Color where
  primaryOrder := seed.primaryOrder
  bodyOrder := seed.bodyOrder
  kernel := MixedKernel.inputIteration (primaryCoordinates seed).reverse
    (fun _ => operator.symm.toLinearMap.comp (boundaryCollapse interior target))
    (inputReference primary body seed) seed.kernel

/-- The activation factors stay outside the joint density; this identity
keeps the full correlated primary kernel. -/
theorem primary_seedOutput_densityForm (primary body : FiniteDist Color)
    (rho : ℝ) (operator : Module.End ℝ (Color → ℝ)) (bodyChannel : Color → Color → ℝ)
    (seed : InputSeed Color) (hbody : seed.bodyOrder=0)
    (hprimary : ∀ color,primary.weight color≠0) :
    seedOutput primary body (fun input output => rho*LinearMap.toMatrix' operator output input) bodyChannel seed=
      MvPolynomial.C (rho^seed.primaryOrder)*jointDensityForm (inputReference primary body seed)
        (MixedKernel.inputIteration (primaryCoordinates seed).reverse (fun _ => operator)
          (inputReference primary body seed) seed.kernel) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Color) (Classical.decEq Color)
  rw [seedOutput_eq_mass,jointDensityForm_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _
  rw [primary_seedOutputMass_iteration primary body rho operator bodyChannel seed hbody hprimary]
  simp only [all_primary_reference primary body seed hbody,map_mul]
  ring

theorem boundaryPrimarySeed_output (primary body : FiniteDist Color)
    (rho : ℝ) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (bodyChannel : Color → Color → ℝ)
    (interior : Finset Color) (target : Color → ℝ)
    (hrange : ∀ profile,operator profile-profile∈canonicalInteriorProfiles interior)
    (hprimary : ∀ color,primary.weight color≠0)
    (seed : InputSeed Color) (hbody : seed.bodyOrder=0) :
    seedOutput primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel
      (boundaryPrimarySeed primary body operator interior target seed)=
      boundaryPolynomial interior target
        (seedOutput primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel seed) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Color) (Classical.decEq Color)
  let coordinates := (primaryCoordinates seed).reverse
  let reference := inputReference primary body seed
  have hnodup : coordinates.Nodup := List.nodup_reverse.mpr (primaryCoordinates_nodup seed)
  have hcomplete : ∀ slot,slot∈coordinates := fun slot =>
    List.mem_reverse.mpr (primaryCoordinates_complete seed hbody slot)
  have hp : ∀ slot color,(reference slot).weight color≠0 := by
    intro slot color
    change (inputReference primary body seed slot).weight color≠0
    rw [all_primary_reference primary body seed hbody slot]
    exact hprimary color
  have hleft : operator.toLinearMap.comp (operator.symm.toLinearMap.comp (boundaryCollapse interior target))=
      boundaryCollapse interior target := by
    apply LinearMap.ext
    intro profile
    funext color
    exact congrFun (operator.apply_symm_apply (boundaryCollapse interior target profile)) color
  have hright : (boundaryCollapse interior target).comp operator.toLinearMap=boundaryCollapse interior target := by
    apply LinearMap.ext
    intro profile
    funext color
    exact congrFun (boundaryCollapse_response_eq interior target operator hrange profile) color
  rw [primary_seedOutput_densityForm primary body rho operator.toLinearMap bodyChannel
    (boundaryPrimarySeed primary body operator interior target seed) hbody hprimary,
    primary_seedOutput_densityForm primary body rho operator.toLinearMap bodyChannel seed hbody hprimary]
  change MvPolynomial.C (rho^seed.primaryOrder)*jointDensityForm reference
      (MixedKernel.inputIteration coordinates (fun _ => operator.toLinearMap) reference
        (MixedKernel.inputIteration coordinates (fun _ => operator.symm.toLinearMap.comp (boundaryCollapse interior target)) reference seed.kernel))=
    boundaryPolynomial interior target
      (MvPolynomial.C (rho^seed.primaryOrder)*jointDensityForm reference
        (MixedKernel.inputIteration coordinates (fun _ => operator.toLinearMap) reference seed.kernel))
  have heleft := congrArg (fun map : Module.End ℝ ((Fin (seed.primaryOrder+seed.bodyOrder) → Color) → ℝ) => map seed.kernel)
    (MixedKernel.inputIteration_comp_all coordinates hnodup hcomplete (fun _ => operator.toLinearMap)
      (fun _ => operator.symm.toLinearMap.comp (boundaryCollapse interior target)) reference hp)
  have heright := congrArg (fun map : Module.End ℝ ((Fin (seed.primaryOrder+seed.bodyOrder) → Color) → ℝ) => map seed.kernel)
    (MixedKernel.inputIteration_comp_all coordinates hnodup hcomplete (fun _ => boundaryCollapse interior target)
      (fun _ => operator.toLinearMap) reference hp)
  simp only [LinearMap.comp_apply,hleft] at heleft
  simp only [LinearMap.comp_apply,hright] at heright
  rw [heleft,map_mul]
  have hC : boundaryPolynomial interior target (MvPolynomial.C (rho^seed.primaryOrder))=MvPolynomial.C (rho^seed.primaryOrder) :=
    (boundaryPolynomial interior target).commutes _
  rw [hC]
  change _=_*profilePolynomialMap (boundaryCollapse interior target) _
  rw [profilePolynomialMap_jointDensityForm _ reference coordinates hnodup hcomplete hp,heright]

theorem boundaryPrimarySeed_activity_le (primary body : FiniteDist Color)
    (primaryPool bodyPool radius bound : ℝ) (hbound : 0≤bound)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (target : Color → ℝ) (seed : InputSeed Color)
    (hoperator : ∀ slot∈(primaryCoordinates seed).reverse,∀ kernel,
      MixedKernel.activity (inputRate primaryPool bodyPool seed) (inputReference primary body seed)
        (MixedKernel.partialInputOperator slot (operator.symm.toLinearMap.comp (boundaryCollapse interior target))
          (inputReference primary body seed slot).weight kernel)≤
      bound*MixedKernel.activity (inputRate primaryPool bodyPool seed) (inputReference primary body seed) kernel)
    (hradius : 0≤radius) :
    inputWeight primary body primaryPool bodyPool radius (boundaryPrimarySeed primary body operator interior target seed)≤
      bound^seed.primaryOrder*inputWeight primary body primaryPool bodyPool radius seed := by
  have hh := MixedKernel.inputIteration_activity_le (primaryCoordinates seed).reverse
    (fun _ => operator.symm.toLinearMap.comp (boundaryCollapse interior target))
    (inputReference primary body seed) (inputRate primaryPool bodyPool seed) bound hbound hoperator seed.kernel
  simp only [List.length_reverse,primaryCoordinates,List.length_ofFn] at hh
  change radius^seed.bodyOrder*MixedKernel.activity _ _ _≤bound^seed.primaryOrder*(radius^seed.bodyOrder*MixedKernel.activity _ _ _)
  exact (mul_le_mul_of_nonneg_left hh (pow_nonneg hradius _)).trans_eq (by ring)

end
end AFT.RepresentedPolynomial

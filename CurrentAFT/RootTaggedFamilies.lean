import CurrentAFT.RootTaggedLocal

/-! The actual singleton root channel in the genuine canonical coefficient family. -/

namespace CurrentAFT.RootTaggedFamilies

open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm DiffuseProfiles
  ProposalPrimary ActualControls UniformBodyProfiles CycleRootExpansion RootTaggedLocal
  BackgroundFamilies BackgroundRates BackgroundEvaluation BackgroundFirstEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  ActualControls.bodyReference CycleRootExpansion.rootReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def rootKernelLinear (security : ℕ) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] canonicalKernels (primaryLaw security) (bodyReference security) 1 0 where
  toFun input := primaryKernel (primaryLaw security) (bodyReference security)
    (rootLift security role queue input) (rootLift_mean security role queue input)
  map_add' first second := by
    apply Subtype.ext
    funext colors centers
    exact congrFun (map_add (rootLift security role queue) first second) (colors 0)
  map_smul' scalar input := by
    apply Subtype.ext
    funext colors centers
    exact congrFun (map_smul (rootLift security role queue) scalar input) (colors 0)

def rootFamilyLinear (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] ActualFamily security order :=
  (LinearMap.single ℝ (fun arity : TruncatedArity order =>
    canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val)
      (BackgroundFamilies.primaryArity order horder)).comp (rootKernelLinear security role queue)

theorem rootFamilyLinear_apply (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    rootFamilyLinear security order horder role queue input =
      primaryFamily (primaryLaw security) (bodyReference security) order horder
        (rootLift security role queue input) (rootLift_mean security role queue input) := by
  funext arity
  by_cases hequal : arity = BackgroundFamilies.primaryArity order horder
  · subst arity
    simp only [rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply,
      primaryFamily, Pi.single_eq_same, rootKernelLinear]
    rfl
  · simp only [rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply,
      primaryFamily, Pi.single_eq_of_ne hequal]

theorem rootFamily_norm (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (rootFamilyLinear security order horder role queue input) ≤
      primaryFactor security * rootCost security * Real.sqrt ((rootReference security).l2Sq input) := by
  rw [rootFamilyLinear_apply, primaryFamily_norm]
  have h := rootLift_norm security role queue input
  exact (mul_le_mul_of_nonneg_left h (by unfold primaryFactor; positivity)).trans_eq (by ring)

theorem rootFamily_norm_decay (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (rootFamilyLinear security order horder role queue input) ≤
      4128 / (Parameters.base security : ℝ) ^ 94 * Real.sqrt ((rootReference security).l2Sq input) := by
  have hb := FirstResponse.base_pos security
  apply (rootFamily_norm security order horder role queue input).trans
  have hpositive : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hcost := mul_le_mul_of_nonneg_left (rootCost_decay security) hpositive
  have hfactor : primaryFactor security * (4128 / (Parameters.base security : ℝ) ^ 30) =
      4128 / (Parameters.base security : ℝ) ^ 94 := by
    rw [primaryFactor_eq]
    field_simp
  rw [hfactor] at hcost
  exact mul_le_mul_of_nonneg_right hcost (Real.sqrt_nonneg _)

theorem rootFamily_image (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    evaluation security order (rootFamilyLinear security order horder role queue input) =
      TruncatedOutput.quotientMap order (AFT.RepresentedPolynomial.profileForm (rootMass security role queue input)) := by
  rw [rootFamilyLinear_apply, primaryFamily_image, rootLift_massLeading]

theorem rootFamily_constant (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    rootFamilyLinear security order horder role queue (fun _ => 1) = 0 := by
  funext arity
  by_cases hequal : arity = BackgroundFamilies.primaryArity order horder
  · subst arity
    simp only [rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_same, Pi.zero_apply]
    change rootKernelLinear security role queue (fun _ => 1) = 0
    apply Subtype.ext
    funext colors centers
    exact congrFun (rootLift_constant security role queue) (colors 0)
  · simp only [rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply, Pi.zero_apply]
    exact Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val) hequal _

end

end CurrentAFT.RootTaggedFamilies

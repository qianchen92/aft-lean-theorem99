import AFT.TensorBoundaryMean
import AFT.PairedBoundaryMean
import AFT.ActualJointBoundary

/-! # The full joint public paired lift in every retained boundary cell -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color Center : Type*} [Fintype Color] [Fintype Center]

/-- The actual paired score as a linear map on input densities. Its public
output records the primary color and the independent compensating center. -/
def pairedPublicDensity (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ) :
    (Color → ℝ) →ₗ[ℝ] ((Color × Center) → ℝ) where
  toFun value pair := value pair.1 - activation *
    (∑ color, anchor color pair.2 * (primary.weight color * value color)) / body.weight pair.2
  map_add' first second := by
    funext pair
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]
    ring
  map_smul' scalar value := by
    funext pair
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have he : (∑ color, anchor color pair.2 * (primary.weight color * (scalar * value color))) =
        scalar * ∑ color, anchor color pair.2 * (primary.weight color * value color) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      ring
    rw [he]
    ring

theorem pairedPublicDensity_eq_lift (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ) (value : Color → ℝ)
    (hprimary : ∀ color, primary.weight color ≠ 0) :
    pairedPublicDensity primary body anchor activation value =
      fun pair => pairedLift primary.weight body.weight anchor activation
        (fun color => primary.weight color * value color) pair.1 pair.2 := by
  funext pair
  simp only [pairedPublicDensity, LinearMap.coe_mk, AddHom.coe_mk, pairedLift, applyAnchor,
    mul_div_cancel_left₀ _ (hprimary pair.1)]

/-- Scalar legal profiles remain centered after the genuine paired lift. -/
theorem pairedPublicDensity_legal_mean_zero (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ)
    (hprimary : ∀ color, primary.weight color ≠ 0)
    (hanchor : ∀ color, ∑ center, anchor color center = 1)
    (hsupport : ∀ profile center, body.weight center = 0 → applyAnchor anchor profile center = 0)
    (interior : Finset Color) (projection : Module.End ℝ (Color → ℝ))
    (hlegal : ∀ profile, (∑ color, projection profile color) = 0 ∧
      ∀ color ∉ interior, projection profile color = 0)
    (record : Option Color)
    (hpos : 0 < primary.eventMass (fun color => FiniteDist.boundaryRecord interior color = record))
    (value : Color → ℝ) :
    ((primary.condition (fun color => FiniteDist.boundaryRecord interior color = record) hpos).prod body).expectation
      (pairedPublicDensity primary body anchor activation
        (MixedKernel.densityConjugate projection primary.weight value)) = 0 := by
  rw [pairedPublicDensity_eq_lift _ _ _ _ _ hprimary]
  have he : (fun color => primary.weight color * MixedKernel.densityConjugate projection primary.weight value color) =
      projection (fun color => primary.weight color * value color) := by
    funext color
    exact mul_div_cancel₀ _ (hprimary color)
  rw [he]
  exact pairedLift_boundary_mean_zero primary body anchor activation _ hprimary hanchor (hsupport _)
    interior (hlegal _).1 (hlegal _).2 record hpos

/-- Arbitrary joint legal inputs have exact zero conditional mean under
the real tensor of paired public scores, including all compensating centers. -/
theorem pairedPublicDensity_joint_boundary_mean_zero (count : ℕ)
    (coordinates : List (Fin count)) (hnodup : coordinates.Nodup)
    (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ)
    (hprimary : ∀ color, primary.weight color ≠ 0)
    (hanchor : ∀ color, ∑ center, anchor color center = 1)
    (hsupport : ∀ profile center, body.weight center = 0 → applyAnchor anchor profile center = 0)
    (interior : Finset Color) (projection : Module.End ℝ (Color → ℝ))
    (hlegal : ∀ profile, (∑ color, projection profile color) = 0 ∧
      ∀ color ∉ interior, projection profile color = 0)
    (record : Fin count → Option Color)
    (hpos : ∀ index, 0 < primary.eventMass (fun color => FiniteDist.boundaryRecord interior color = record index))
    (kernel : (Fin count → Color) → ℝ) :
    (FiniteDist.independent (fun index =>
      (primary.condition (fun color => FiniteDist.boundaryRecord interior color = record index) (hpos index)).prod body)).expectation
      (TensorChannel.applyLinear count (fun _ => pairedPublicDensity primary body anchor activation)
        (MixedKernel.jointLegalProjection coordinates (fun _ => projection) (fun _ => primary) kernel)) = 0 := by
  exact TensorChannel.jointLegalProjection_channel_mean_zero count coordinates hnodup _ (fun _ => hprimary)
    _ _ _ (fun index value => pairedPublicDensity_legal_mean_zero primary body anchor activation hprimary hanchor
      hsupport interior projection hlegal (record index) (hpos index) value) kernel

end
end AFT

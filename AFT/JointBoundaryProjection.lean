import AFT.MixedCoordinateProducts
import AFT.BoundaryCentering
import AFT.Inverse
import AFT.FiniteExpectationAlgebra

/-! # The full joint boundary ideal and its exact conditional centering -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

theorem expectation_productKernel (reference : Slot → FiniteDist Color) (functions : Slot → Color → ℝ) :
    (FiniteDist.independent reference).expectation (productKernel functions) =
      ∏ slot, (reference slot).expectation (functions slot) := by
  unfold FiniteDist.expectation FiniteDist.independent productKernel
  simp only [← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

/-- Scalar conditional mean preservation tensorizes on arbitrary joint
kernels through a finite spanning expansion, with no factorization hypothesis. -/
theorem inputIteration_preserves_expectation (coordinates : List Slot) (hnodup : coordinates.Nodup)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference conditional : Slot → FiniteDist Color)
    (hscalar : ∀ slot ∈ coordinates, ∀ value : Color → ℝ,
      (conditional slot).expectation (densityConjugate (operator slot) (reference slot).weight value) =
        (conditional slot).expectation value)
    (kernel : (Slot → Color) → ℝ) :
    (FiniteDist.independent conditional).expectation (inputIteration coordinates operator reference kernel) =
      (FiniteDist.independent conditional).expectation kernel := by
  have hp (functions : Slot → Color → ℝ) :
      (FiniteDist.independent conditional).expectation (inputIteration coordinates operator reference (productKernel functions)) =
        (FiniteDist.independent conditional).expectation (productKernel functions) := by
    rw [inputIteration_product coordinates hnodup, expectation_productKernel, expectation_productKernel]
    apply Finset.prod_congr rfl
    intro slot _
    by_cases hs : slot ∈ coordinates
    · simpa only [if_pos hs] using hscalar slot hs (functions slot)
    · simp only [if_neg hs]
  let average : ((Slot → Color) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := (FiniteDist.independent conditional).expectation
    map_add' := fun f g => FiniteDist.expectation_add _ f g
    map_smul' := fun scalar f => FiniteDist.expectation_const_mul _ scalar f }
  change average (inputIteration coordinates operator reference kernel) = average kernel
  rw [kernel_product_expansion kernel]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro point _
  exact congrArg (fun value => kernel point * value) (hp _)

/-- The scalar legal projection's density has zero mean in every retained
boundary cell because its profile is mass zero and supported in the interior. -/
theorem legal_density_boundary_mean_zero (primary : FiniteDist Color) (interior : Finset Color)
    (hprimary : ∀ color, primary.weight color ≠ 0)
    (projection : Module.End ℝ (Color → ℝ))
    (hlegal : ∀ profile, (∑ color, projection profile color) = 0 ∧
      ∀ color ∉ interior, projection profile color = 0)
    (record : Option Color)
    (hpos : 0 < primary.eventMass (fun color => FiniteDist.boundaryRecord interior color = record))
    (value : Color → ℝ) :
    (primary.condition (fun color => FiniteDist.boundaryRecord interior color = record) hpos).expectation
      (densityConjugate projection primary.weight value) = 0 := by
  apply FiniteDist.boundary_condition_centered primary interior record hpos
  · unfold FiniteDist.expectation densityConjugate
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have he (color) : primary.weight color *
        (projection (fun input => primary.weight input * value input) color / primary.weight color) =
        projection (fun input => primary.weight input * value input) color := mul_div_cancel₀ _ (hprimary color)
    simp_rw [he]
    exact (hlegal _).1
  · intro color hout
    change projection (fun input => primary.weight input * value input) color / primary.weight color = 0
    rw [(hlegal _).2 color hout, zero_div]

/-- Id minus the product of the scalar complementary projections. In
particular this does not require every primary coordinate to vanish on the boundary. -/
def jointLegalProjection (coordinates : List Slot)
    (projection : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color) :
    Module.End ℝ ((Slot → Color) → ℝ) :=
  LinearMap.id - inputIteration coordinates (fun slot => LinearMap.id - projection slot) reference

/-- The full joint legal input has exact zero conditional mean after all
boundary records are retained. This is the whole boundary ideal. -/
theorem jointLegalProjection_boundary_mean_zero (coordinates : List Slot) (hnodup : coordinates.Nodup)
    (reference : Slot → FiniteDist Color) (interior : Slot → Finset Color)
    (hreference : ∀ slot color, (reference slot).weight color ≠ 0)
    (projection : Slot → Module.End ℝ (Color → ℝ))
    (hlegal : ∀ slot, ∀ profile, (∑ color, projection slot profile color) = 0 ∧
      ∀ color ∉ interior slot, projection slot profile color = 0)
    (record : Slot → Option Color)
    (hpos : ∀ slot, 0 < (reference slot).eventMass
      (fun color => FiniteDist.boundaryRecord (interior slot) color = record slot))
    (kernel : (Slot → Color) → ℝ) :
    (FiniteDist.independent (fun slot => (reference slot).condition
      (fun color => FiniteDist.boundaryRecord (interior slot) color = record slot) (hpos slot))).expectation
      (jointLegalProjection coordinates projection reference kernel) = 0 := by
  have hs (slot) (value : Color → ℝ) :
      densityConjugate (LinearMap.id - projection slot) (reference slot).weight value =
        value - densityConjugate (projection slot) (reference slot).weight value := by
    funext color
    change ((reference slot).weight color * value color -
      projection slot (fun input => (reference slot).weight input * value input) color) /
      (reference slot).weight color = _
    rw [sub_div, mul_div_cancel_left₀ _ (hreference slot color)]
    rfl
  have he := inputIteration_preserves_expectation coordinates hnodup
    (fun slot => LinearMap.id - projection slot) reference
    (fun slot => (reference slot).condition
      (fun color => FiniteDist.boundaryRecord (interior slot) color = record slot) (hpos slot))
    (fun slot _ value => by
      rw [hs]
      change (FiniteDist.expectation _ (fun color => value color -
        densityConjugate (projection slot) (reference slot).weight value color)) = _
      rw [FiniteDist.expectation_sub,
        legal_density_boundary_mean_zero (reference slot) (interior slot) (hreference slot)
          (projection slot) (hlegal slot) (record slot) (hpos slot), sub_zero]) kernel
  change (FiniteDist.independent _).expectation (fun word => kernel word - inputIteration _ _ _ kernel word) = 0
  rw [FiniteDist.expectation_sub, he, sub_self]

end
end AFT.MixedKernel

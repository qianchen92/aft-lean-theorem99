import AFT.JointBoundaryProjection
import AFT.PrimarySeedCanonical
import AFT.MixedProducts

/-! # Exact tensor conjugacy and activity of the whole boundary ideal -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- Checking the product spanning family is sufficient for a linear
identity on an arbitrary finite joint input table. -/
theorem linear_eq_of_products (first second : Module.End ℝ ((Slot → Color) → ℝ))
    (h : ∀ functions : Slot → Color → ℝ, first (productKernel functions) = second (productKernel functions)) :
    first = second := by
  apply LinearMap.ext
  intro kernel
  rw [kernel_product_expansion kernel, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro point _
  rw [map_smul, map_smul, h]

omit [Fintype Slot] [DecidableEq Slot] [Fintype Color] in
theorem densityConjugate_comp (first second : Module.End ℝ (Color → ℝ))
    (reference : Color → ℝ) (hpositive : ∀ color, reference color ≠ 0) (value : Color → ℝ) :
    densityConjugate first reference (densityConjugate second reference value) =
      densityConjugate (first.comp second) reference value := by
  funext color
  unfold densityConjugate
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  have he : (fun input => reference input *
      (second (fun inner => reference inner * value inner) input / reference input)) =
      second (fun inner => reference inner * value inner) := by
    funext input
    exact mul_div_cancel₀ _ (hpositive input)
  rw [he]

/-- Full tensor composition is coordinatewise profile composition, on the
literal joint kernel and with every reference-weight cancellation checked. -/
theorem inputIteration_comp_all (coordinates : List Slot) (hnodup : coordinates.Nodup)
    (hcomplete : ∀ slot, slot ∈ coordinates)
    (first second : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (hpositive : ∀ slot color, (reference slot).weight color ≠ 0) :
    (inputIteration coordinates first reference).comp (inputIteration coordinates second reference) =
      inputIteration coordinates (fun slot => (first slot).comp (second slot)) reference := by
  apply linear_eq_of_products
  intro functions
  simp only [LinearMap.comp_apply, inputIteration_product coordinates hnodup,
    if_pos (hcomplete _)]
  congr 1
  funext slot
  exact densityConjugate_comp (first slot) (second slot) (reference slot).weight (hpositive slot) (functions slot)

/-- The actual joint legal projection is the conjugate of the entire
output boundary ideal, rather than a product of one-coordinate ideals. -/
theorem jointLegalProjection_evaluation (coordinates : List Slot) (hnodup : coordinates.Nodup)
    (hcomplete : ∀ slot, slot ∈ coordinates) (reference : Slot → FiniteDist Color)
    (hpositive : ∀ slot color, (reference slot).weight color ≠ 0)
    (operator : Slot → ((Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)))
    (projection : Slot → Module.End ℝ (Color → ℝ)) :
    (inputIteration coordinates (fun slot => (operator slot).toLinearMap) reference).comp
      (jointLegalProjection coordinates (fun slot => legalInputProjection (operator slot) (projection slot)) reference) =
    (jointLegalProjection coordinates projection reference).comp
      (inputIteration coordinates (fun slot => (operator slot).toLinearMap) reference) := by
  unfold jointLegalProjection
  rw [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id, LinearMap.id_comp,
    inputIteration_comp_all coordinates hnodup hcomplete _ _ reference hpositive,
    inputIteration_comp_all coordinates hnodup hcomplete _ _ reference hpositive]
  congr 2
  funext slot
  apply LinearMap.ext
  intro profile
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    map_sub, LinearEquiv.coe_coe, legalInputProjection_evaluation]

/-- A scalar mass-zero projection leaves the complementary profile mass
unchanged. Therefore the entire joint ideal preserves canonicality. -/
theorem jointLegalProjection_canonical (coordinates : List Slot)
    (reference : Slot → FiniteDist Color) (hpositive : ∀ slot color, (reference slot).weight color ≠ 0)
    (projection : Slot → Module.End ℝ (Color → ℝ))
    (hmass : ∀ slot profile, (∑ color, projection slot profile color) = 0)
    (kernel : (Slot → Color) → ℝ) (hc : Hoeffding.Canonical reference Finset.univ kernel) :
    Hoeffding.Canonical reference Finset.univ (jointLegalProjection coordinates projection reference kernel) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have ht := inputIteration_canonical coordinates (fun slot => LinearMap.id - projection slot) reference
    (fun slot _ => hpositive slot) (fun slot _ profile => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, Finset.sum_sub_distrib, hmass, sub_zero]) kernel hc
  constructor
  · intro first second heq
    have hh : first = second := funext fun slot => heq slot (Finset.mem_univ slot)
    rw [hh]
  · intro slot hs word
    simp only [jointLegalProjection, LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hc.2 slot hs word, ht.2 slot hs word, sub_self]

/-- The joint projection has a fixed-order activity cost in the specified
mixed-fiber norm; the constant is independent of the palette and pool sizes. -/
theorem jointLegalProjection_activity_le (coordinates : List Slot)
    (reference : Slot → FiniteDist Color) (rates : Slot → ℝ) (hrates : ∀ slot, 0 ≤ rates slot)
    (projection : Slot → Module.End ℝ (Color → ℝ)) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hcomplement : ∀ slot ∈ coordinates, ∀ kernel : (Slot → Color) → ℝ,
      activity rates reference (partialInputOperator slot (LinearMap.id - projection slot) (reference slot).weight kernel) ≤
        constant * activity rates reference kernel)
    (kernel : (Slot → Color) → ℝ) :
    activity rates reference (jointLegalProjection coordinates projection reference kernel) ≤
      (1 + constant ^ coordinates.length) * activity rates reference kernel := by
  change activity rates reference (kernel - inputIteration coordinates _ reference kernel) ≤ _
  apply (activity_sub_le rates reference _ _ hrates).trans
  have he := inputIteration_activity_le coordinates _ reference rates constant hconstant hcomplement kernel
  linarith

end
end AFT.MixedKernel

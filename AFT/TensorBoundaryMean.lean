import AFT.JointBoundaryAlgebra
import AFT.TensorChannelFormula

/-! # Joint legal projections remain centered through public tensor lifts -/
namespace AFT.TensorChannel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Input Output : Type*} [Fintype Input] [Fintype Output]

omit [Fintype Output] in
/-- Exact tensor action on the spanning product family. -/
theorem applyLinear_product (count : ℕ)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (functions : Fin count → Input → ℝ) :
    applyLinear count channel (MixedKernel.productKernel functions) =
      MixedKernel.productKernel (fun index => channel index (functions index)) := by
  funext output
  rw [show applyLinear count channel _ output = apply count channel _ output from rfl, apply_formula]
  simp only [MixedKernel.productKernel, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ index : Fin count, ∑ color : Input, functions index color * channel index (Pi.single color 1) (output index) := by
      have he := Fintype.prod_sum (fun (index : Fin count) (color : Input) =>
        functions index color * channel index (Pi.single color 1) (output index))
      refine Eq.trans ?_ he.symm
      apply Finset.sum_congr (by ext; simp)
      intro word _
      rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro index _
      exact (channel_sum_single (channel index) (functions index) (output index)).symm

/-- Scalar mean-zero legal directions imply exact centering of the full
joint boundary ideal after an arbitrary tensor public lift. The input
kernel is arbitrary, rather than a rank-one product. -/
theorem jointLegalProjection_channel_mean_zero (count : ℕ)
    (coordinates : List (Fin count)) (hnodup : coordinates.Nodup)
    (reference : Fin count → FiniteDist Input)
    (hpositive : ∀ index color, (reference index).weight color ≠ 0)
    (projection : Fin count → Module.End ℝ (Input → ℝ))
    (output : Fin count → FiniteDist Output)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (hscalar : ∀ index value, (output index).expectation
      (channel index (MixedKernel.densityConjugate (projection index) (reference index).weight value)) = 0)
    (kernel : (Fin count → Input) → ℝ) :
    (FiniteDist.independent output).expectation (applyLinear count channel
      (MixedKernel.jointLegalProjection coordinates projection reference kernel)) = 0 := by
  let average : ((Fin count → Output) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := (FiniteDist.independent output).expectation
    map_add' := fun f g => FiniteDist.expectation_add _ f g
    map_smul' := fun scalar f => FiniteDist.expectation_const_mul _ scalar f }
  let functional := average.comp (applyLinear count channel)
  have hcomp (index) (value : Input → ℝ) :
      MixedKernel.densityConjugate (LinearMap.id - projection index) (reference index).weight value =
        value - MixedKernel.densityConjugate (projection index) (reference index).weight value := by
    funext color
    change ((reference index).weight color * value color -
      projection index (fun input => (reference index).weight input * value input) color) /
      (reference index).weight color = _
    rw [sub_div, mul_div_cancel_left₀ _ (hpositive index color)]
    rfl
  have hproduct (functions : Fin count → Input → ℝ) :
      functional (MixedKernel.inputIteration coordinates (fun index => LinearMap.id - projection index)
        reference (MixedKernel.productKernel functions)) = functional (MixedKernel.productKernel functions) := by
    dsimp only [functional, LinearMap.comp_apply]
    rw [MixedKernel.inputIteration_product coordinates hnodup, applyLinear_product, applyLinear_product]
    change (FiniteDist.independent output).expectation (MixedKernel.productKernel _) =
      (FiniteDist.independent output).expectation (MixedKernel.productKernel _)
    rw [MixedKernel.expectation_productKernel, MixedKernel.expectation_productKernel]
    apply Finset.prod_congr rfl
    intro index _
    by_cases hi : index ∈ coordinates
    · simp only [if_pos hi, hcomp, map_sub]
      change (output index).expectation (fun point => channel index (functions index) point -
        channel index (MixedKernel.densityConjugate (projection index) (reference index).weight (functions index)) point) = _
      rw [FiniteDist.expectation_sub, hscalar, sub_zero]
    · simp only [if_neg hi]
  have hfull : functional (MixedKernel.inputIteration coordinates (fun index => LinearMap.id - projection index)
      reference kernel) = functional kernel := by
    rw [MixedKernel.kernel_product_expansion kernel]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro point _
    exact congrArg (fun value => kernel point * value) (hproduct _)
  change functional (MixedKernel.jointLegalProjection coordinates projection reference kernel) = 0
  unfold MixedKernel.jointLegalProjection
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hfull, sub_self]

end
end AFT.TensorChannel

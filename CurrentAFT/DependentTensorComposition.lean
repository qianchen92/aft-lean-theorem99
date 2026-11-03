import AFT.DependentTensorChannel

/-! # Composition of true dependent tensor channels -/
namespace CurrentAFT.DependentTensorComposition
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Middle Output : Index → Type*}
  [∀ index, Fintype (Input index)] [∀ index, Fintype (Middle index)] [∀ index, Fintype (Output index)]

omit [∀ index, Fintype (Output index)] in
theorem apply_comp
    (first : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Middle index → ℝ))
    (second : ∀ index, (Middle index → ℝ) →ₗ[ℝ] (Output index → ℝ))
    (input : ((index : Index) → Input index) → ℝ) :
    DependentTensorChannel.apply (fun index => (second index).comp (first index)) input =
      DependentTensorChannel.apply second (DependentTensorChannel.apply first input) := by
  funext output
  unfold DependentTensorChannel.apply
  simp only [LinearMap.comp_apply]
  have hcolumn (index : Index) (source : Input index) :
      second index (first index (Pi.single source 1)) (output index) =
        ∑ middle, first index (Pi.single source 1) middle *
          second index (Pi.single middle 1) (output index) :=
    TensorChannel.channel_sum_single (second index) _ _
  simp_rw [hcolumn]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle _
  apply Finset.sum_congr rfl
  intro source _
  rw [Finset.prod_mul_distrib]
  ring

end
end CurrentAFT.DependentTensorComposition

import CurrentAFT.DependentTensorComposition

/-! # Exact algebra-valued contraction of arbitrary joint finite inputs

This is a literal source sum of products of local linear columns. It is
not a product assumption on the input kernel. Coordinate projections may
be moved to the complete joint input before physical polynomial evaluation.
-/
namespace CurrentAFT.FinitePolynomialTensor
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Middle : Index → Type*} [∀ index, Fintype (Input index)] [∀ index, Fintype (Middle index)]
  {Value : Type*} [CommRing Value] [Algebra ℝ Value]

theorem linear_expansion {Source : Type*} [Fintype Source]
    (channel : (Source → ℝ) →ₗ[ℝ] Value) (score : Source → ℝ) :
    channel score = ∑ source, score source • channel (Pi.single source 1) := by
  classical
  have hscore : score = ∑ source, score source • (Pi.single source 1 : Source → ℝ) := by
    funext point
    simp [Pi.single_apply]
  conv_lhs => rw [hscore]
  simp only [map_sum, map_smul]

def synthesis (channels : ∀ index, (Input index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → Input index) → ℝ) : Value :=
  ∑ source, input source • ∏ index, channels index (Pi.single (source index) 1)

def synthesisLinear (channels : ∀ index, (Input index → ℝ) →ₗ[ℝ] Value) :
    ((((index : Index) → Input index) → ℝ) →ₗ[ℝ] Value) where
  toFun := synthesis channels
  map_add' first second := by simp only [synthesis, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    simp only [synthesis, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem synthesis_comp
    (preprocess : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Middle index → ℝ))
    (channels : ∀ index, (Middle index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → Input index) → ℝ) :
    synthesis (fun index => (channels index).comp (preprocess index)) input =
      synthesis channels (DependentTensorChannel.apply preprocess input) := by
  unfold synthesis
  simp only [LinearMap.comp_apply]
  have hcolumn (index : Index) (source : Input index) :
      channels index (preprocess index (Pi.single source 1)) =
        ∑ middle, preprocess index (Pi.single source 1) middle • channels index (Pi.single middle 1) :=
    linear_expansion (channels index) _
  simp_rw [hcolumn, Fintype.prod_sum]
  simp only [Finset.prod_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  unfold DependentTensorChannel.apply
  simp only [Finset.sum_smul]

theorem synthesis_comp_fixed
    (preprocess : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (channels : ∀ index, (Input index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → Input index) → ℝ)
    (hfixed : DependentTensorChannel.apply preprocess input = input) :
    synthesis (fun index => (channels index).comp (preprocess index)) input = synthesis channels input := by
  rw [synthesis_comp, hfixed]

theorem synthesis_mul_product
    (channels physical : ∀ index, (Input index → ℝ) →ₗ[ℝ] Value) (denominator : Index → Value)
    (hcolumn : ∀ index source, channels index (Pi.single source 1) * denominator index =
      physical index (Pi.single source 1))
    (input : ((index : Index) → Input index) → ℝ) :
    synthesis channels input * (∏ index, denominator index) = synthesis physical input := by
  unfold synthesis
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  rw [smul_mul_assoc, ← Finset.prod_mul_distrib]
  simp only [hcolumn]

variable {Output : Type*} [CommRing Output] [Algebra ℝ Output]

theorem map_synthesis (map : Value →ₐ[ℝ] Output)
    (channels : ∀ index, (Input index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → Input index) → ℝ) :
    map (synthesis channels input) = synthesis (fun index => map.toLinearMap.comp (channels index)) input := by
  simp only [synthesis, map_sum, map_smul, map_prod, LinearMap.comp_apply, AlgHom.toLinearMap_apply]

end
end CurrentAFT.FinitePolynomialTensor

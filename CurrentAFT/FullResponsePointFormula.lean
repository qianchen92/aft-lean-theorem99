import CurrentAFT.CalibrationPointCoordinates
import CurrentAFT.FullResponseEnumeration

/-! # The exact bounded-enumeration formula for each full response column

A column has one source arity and one joint centered point kernel. Its root
part averages the actual distinct control choices and only root tags of size
at most the fixed order. The common queue stays outside each full product.
-/
namespace CurrentAFT.FullResponsePointFormula
open AFT ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  GradedControlAlgebra LocalCoefficientFamily ActualCompleteStability
  CalibrationPointCoordinates ActualRootFamily ActualBlockFock
  TaggedSelection UniformTaggedOutput BackgroundRates ActualBackground FullResponseEnumeration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance pointFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  primaryLaw bodyReference ordinaryPool

abbrev Index (security order : ℕ) := PointIndex (ActualControls.Palette security) (SafePalette security) order

def referenceWeight (security order : ℕ) (source : Index security order) : ℝ :=
  (∏ index, (primaryLaw security).weight (source.2.1 index)) *
    ∏ index, (bodyReference security).weight (source.2.2 index)

def basisFamily (security order : ℕ) (source : Index security order) : Family security order :=
  Pi.single source.1 (pointKernel (primaryLaw security) (bodyReference security)
    (primaryReference_positive security) (bodyReference_positive security) source.2.1 source.2.2)

theorem decoded_column (security order : ℕ) (source : Index security order) :
    decode (primaryLaw security) (bodyReference security) (primaryReference_positive security)
      (bodyReference_positive security) order (Pi.single source 1) =
        referenceWeight security order source • basisFamily security order source := by
  rcases source with ⟨sourceArity, sourcePrimary, sourceBody⟩
  funext arity
  by_cases hequal : arity = sourceArity
  · subst arity
    simp [decode, referenceWeight, basisFamily, Pi.single_apply, ite_and]
  · have hzero (colors : Fin arity.val.1.val → ActualControls.Palette security)
        (centers : Fin arity.val.2.val → SafePalette security) :
        (Pi.single (M := fun _ : Index security order => ℝ)
          ⟨sourceArity, sourcePrimary, sourceBody⟩ (1 : ℝ)) ⟨arity, colors, centers⟩ = 0 := by
      have hne : (⟨arity, colors, centers⟩ : Index security order) ≠
          ⟨sourceArity, sourcePrimary, sourceBody⟩ := fun h => hequal (congrArg Sigma.fst h)
      exact Pi.single_eq_of_ne (M := fun _ : Index security order => ℝ) hne (1 : ℝ)
    simp only [decode, LinearMap.coe_mk, AddHom.coe_mk, hzero, mul_zero, zero_smul,
      Finset.sum_const_zero, Pi.smul_apply, basisFamily, Pi.single_eq_of_ne hequal, smul_zero]

theorem rootLinear_single (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (arity : TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val) :
    rootLinear security order horder hroom queue layout (Pi.single arity kernel) =
      selectedAverage security order horder hroom queue layout arity kernel := by
  rw [rootLinear_apply, Finset.sum_eq_single arity]
  · rw [Pi.single_eq_same]
  · intro other _ hother
    rw [Pi.single_eq_of_ne hother, map_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

def rootPointResponse (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (source : Index security order) : Family security order :=
  ∑ choice : Choice security source.1.val.1.val source.1.val.2.val,
    (choiceLaw security _ _ (primary_room security order hroom source.1)
      (body_room security order hroom source.1)).weight choice •
      ∑ tagged ∈ (boundedSubsets (BlockIndex security) order).filter (fun tagged => 2 ≤ tagged.card),
        ActualRootResponse.response order horder queue (selection security _ _ choice) tagged layout
          (pointKernel (primaryLaw security) (bodyReference security) (primaryReference_positive security)
            (bodyReference_positive security) source.2.1 source.2.2)

theorem rootLinear_basis (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (source : Index security order) :
    rootLinear security order horder hroom queue layout (basisFamily security order source) =
      rootPointResponse security order horder hroom queue layout source := by
  rw [basisFamily, rootLinear_single, selectedAverage_apply]
  unfold rootPointResponse
  apply Finset.sum_congr rfl
  intro choice _
  congr 1
  rw [selectedDefect_bounded]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_congr (by ext tagged; simp [mem_boundedSubsets])
  intro tagged _
  rfl

def pointResponse (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (source : Index security order) : Family security order :=
  background security order horder *
    (basisFamily security order source + CompleteRaising.raisingLinear security order (by omega)
      (basisFamily security order source)) +
    ∑ scalar : FirstHistogram.Scalar security, (DiffuseProfiles.scalarLaw security).weight scalar •
      (fixedQueueBackground security order horder scalar.val *
        rootPointResponse security order (by omega) hroom scalar.val layout source)

theorem fullResponse_basis (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (source : Index security order) :
    fullResponse security order horder hroom layout (basisFamily security order source) =
      pointResponse security order horder hroom layout source := by
  simp only [fullResponse, LinearMap.add_apply, independentResponse, rootCorrection,
    LinearMap.coe_mk, AddHom.coe_mk, rootLinear_basis, pointResponse]

theorem currentMatrix_entry (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (output source : Index security order) :
    currentMatrix security order horder hsecurity layout output source =
      (if output = source then 1 else 0) -
        referenceWeight security order source *
          (basisFamily security order source output.1).val output.2.1 output.2.2 +
        referenceWeight security order source *
          (pointResponse security order horder (room security order horder hsecurity) layout source output.1).val
            output.2.1 output.2.2 := by
  simp only [currentMatrix, LinearMap.toMatrix'_apply, extend, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, decoded_column, map_smul, fullResponse_basis, map_sub]
  simp only [encode, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Pi.single_apply]
  split_ifs <;> ring

end
end CurrentAFT.FullResponsePointFormula

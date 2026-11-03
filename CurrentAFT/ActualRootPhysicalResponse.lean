import CurrentAFT.ActualRootResponse
import CurrentAFT.RootSelectedPhysicalLinear
import CurrentAFT.RootUnselectedPhysicalLinear
import CurrentAFT.FinitePolynomialTensor

/-! # Exact physical image of the actual joint root-subset response -/
namespace CurrentAFT.ActualRootPhysicalResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra LocalCoefficientFamily
  RootLocalDenominators FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

private theorem univ_finOne_toList : (Finset.univ : Finset (Fin 1)).toList = [0] := by
  apply Finset.toList_eq_singleton_iff.mpr
  ext index
  rw [Fin.eq_zero index]
  simp

theorem primary_rootProjector {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    PairedRootProjection.projector selection tagged (.inl (.inl index)) =
      RootPrimaryGroupedChannel.projector security (ActualRootGroupedChannel.primaryFlags selection tagged index) := rfl

theorem ordinary_rootProjector {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) :
    PairedRootProjection.projector selection tagged (.inl (.inr index)) =
      RootOrdinaryGroupedChannel.projector security (ActualRootGroupedChannel.ordinaryFlag selection tagged index) := by
  change RootCoordinateProjection.sequence (rootReference security)
    ((Finset.univ : Finset (Fin 1)).toList.map (fun slot =>
      (slot, decide (rootEmbedding selection tagged ⟨.inl (.inr index), slot⟩ ∈ tagged)))) = _
  simp only [univ_finOne_toList, List.map_cons, List.map_nil, RootCoordinateProjection.sequence,
    LinearMap.comp_id]
  rfl

theorem kept_rootProjector {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : HitKept selection tagged) :
    PairedRootProjection.projector selection tagged (.inr index) =
      RootCoordinateProjection.center (rootReference security) (0 : Fin 1) := by
  change RootCoordinateProjection.sequence (rootReference security)
    ((Finset.univ : Finset (Fin 1)).toList.map (fun slot =>
      (slot, decide (rootEmbedding selection tagged ⟨.inr index, slot⟩ ∈ tagged)))) = _
  simp only [univ_finOne_toList, List.map_cons, List.map_nil, RootCoordinateProjection.sequence,
    LinearMap.comp_id]
  have hroot : rootEmbedding selection tagged ⟨.inr index, (0 : Fin 1)⟩ = index.val.val := rfl
  rw [hroot]
  simp only [index.property, decide_true, RootCoordinateProjection.coordinate, if_true]

def localDenominator {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged →
      MvPolynomial (ActualControls.Palette security) ℝ
  | .inl (.inl _) => primaryPolynomial security
  | .inl (.inr _) => ordinaryPolynomial security
  | .inr index => RootUnselectedBlockChannel.positivePolynomial security queue index.val.val

def rawPhysical {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : (group : ActiveGroup selection tagged) →
      (ActualRootGroupedChannel.Input selection tagged group → ℝ) →ₗ[ℝ] MvPolynomial (ActualControls.Palette security) ℝ
  | .inl (.inl _) => RootSelectedPhysicalLinear.primaryRaw security
  | .inl (.inr _) => RootSelectedPhysicalLinear.ordinaryRaw security
  | .inr index => RootUnselectedPhysicalLinear.raw security queue index.val.val

def projectedPhysical {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    (ActualRootGroupedChannel.Input selection tagged group → ℝ) →ₗ[ℝ] MvPolynomial (ActualControls.Palette security) ℝ :=
  (rawPhysical queue selection tagged group).comp
    ((RootSelectedControlCenter.projector selection tagged group).comp
      (PairedRootProjection.projector selection tagged group))

theorem local_physical {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (group : ActiveGroup selection tagged) (score : ActualRootGroupedChannel.Input selection tagged group → ℝ) :
    BackgroundEvaluation.evaluation security order (ActualRootGroupedChannel.channel order horder queue selection tagged group score) *
      TruncatedOutput.quotientMap order (localDenominator queue selection tagged group) =
        TruncatedOutput.quotientMap order (projectedPhysical queue selection tagged group score) := by
  rcases group with (primary | ordinary) | kept
  · change BackgroundEvaluation.evaluation security order
      (RootPrimaryGroupedChannel.channel security order (ActualRootGroupedChannel.primaryFlags selection tagged primary) score) *
        TruncatedOutput.quotientMap order (primaryPolynomial security) = _
    simp only [projectedPhysical, rawPhysical, RootSelectedControlCenter.projector, primary_rootProjector]
    exact RootSelectedPhysicalLinear.primary_physical security order _ score
  · change BackgroundEvaluation.evaluation security order
      (RootOrdinaryGroupedChannel.channel security order horder (ActualRootGroupedChannel.ordinaryFlag selection tagged ordinary) score) *
        TruncatedOutput.quotientMap order (ordinaryPolynomial security) = _
    simp only [projectedPhysical, rawPhysical, RootSelectedControlCenter.projector, ordinary_rootProjector]
    exact RootSelectedPhysicalLinear.ordinary_physical security order horder _ score
  · change BackgroundEvaluation.evaluation security order
      (RootUnselectedGrouped.channel security order horder queue kept.val.val score) *
        TruncatedOutput.quotientMap order (RootUnselectedBlockChannel.positivePolynomial security queue kept.val.val) = _
    simp only [projectedPhysical, rawPhysical, RootSelectedControlCenter.projector, kept_rootProjector,
      LinearMap.id_comp]
    exact RootUnselectedPhysicalLinear.channel_physical security order horder queue kept.val.val score

/-- Both the mask and control centering fix the one actual joint input.
Their removal occurs before any physical polynomial evaluation. -/
theorem synthesis_projected_eq {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    synthesis (projectedPhysical queue selection tagged) (jointInput selection tagged layout kernel) =
      synthesis (rawPhysical queue selection tagged) (jointInput selection tagged layout kernel) := by
  change synthesis (fun group =>
    ((rawPhysical queue selection tagged group).comp (RootSelectedControlCenter.projector selection tagged group)).comp
      (PairedRootProjection.projector selection tagged group)) (jointInput selection tagged layout kernel) = _
  rw [synthesis_comp, PairedRootProjection.projected_jointInput,
    synthesis_comp, RootSelectedControlCenter.projected_jointInput]

/-- Exact physical quotient identity for the complete actual root response.
All local reciprocals cancel against their literal physical denominators. -/
theorem response_physical_active_denominator {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (queue : ℤ) (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    BackgroundEvaluation.evaluation security order
      (ActualRootResponse.response order horder queue selection tagged layout kernel) *
        TruncatedOutput.quotientMap order (∏ group, localDenominator queue selection tagged group) =
      TruncatedOutput.quotientMap order
        (synthesis (rawPhysical queue selection tagged) (jointInput selection tagged layout kernel)) := by
  have hresponse : BackgroundEvaluation.evaluation security order
      (ActualRootResponse.response order horder queue selection tagged layout kernel) =
      synthesis (fun group => (BackgroundEvaluation.evaluation security order).toLinearMap.comp
        (ActualRootGroupedChannel.channel order horder queue selection tagged group))
          (jointInput selection tagged layout kernel) := by
    rw [ActualRootResponse.response_apply, GroupedFamilyIdentity.response_eq]
    simp only [map_sum, map_smul, map_prod, synthesis, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [hresponse, map_prod]
  rw [synthesis_mul_product
    (fun group => (BackgroundEvaluation.evaluation security order).toLinearMap.comp
      (ActualRootGroupedChannel.channel order horder queue selection tagged group))
    (fun group => (TruncatedOutput.quotientMap order).toLinearMap.comp (projectedPhysical queue selection tagged group))
    (fun group => TruncatedOutput.quotientMap order (localDenominator queue selection tagged group))
    (fun group source => by
      simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using
        local_physical order horder queue selection tagged group (Pi.single source 1))]
  rw [← map_synthesis, synthesis_projected_eq]

end
end CurrentAFT.ActualRootPhysicalResponse

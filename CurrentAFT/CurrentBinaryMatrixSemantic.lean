import CurrentAFT.CurrentBinaryFallbackSemantic
import CurrentAFT.CurrentBinaryLoadSemantic

/-! Executed binary inversion of the actual public load columns is the
analytic integral affine matrix. No extension-correction witness is run. -/
namespace CurrentAFT.CurrentBinaryMatrixSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

noncomputable section

 theorem native_inverse_eq (security : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (count : ℕ) (hc : count = CurrentAffineGeometry.edgeCount security)
    (modulus : List Bool) (hm : value modulus = Parameters.modulus security)
    (injection load : Vector IntegerBits (count + 1))
    (hi : ∀ vertex, (injection.get vertex).decode = if vertex.val < Parameters.modulus security then 1 else 0)
    (target : Fin (Parameters.dimension security) → ℤ)
    (hl : ∀ vertex, (load.get vertex).decode = CurrentAffineLoad.rounding security target
      (CurrentAffineGeometry.dimensionEquiv security (vertex.cast (congrArg (fun n => n + 1) hc)))) :
    CurrentAffineLoad.packSource security
      ((fun edge => ((binaryRoundingInverse count modulus injection load).edges.get (edge.cast hc.symm)).decode),
        (binaryRoundingInverse count modulus injection load).charge.decode) = target := by
  subst count
  apply CurrentAffineEmissionBridge.binary_inverse_eq security layout modulus hm injection load
    (fun vertex => hi vertex) target
  intro vertex
  simpa only [Fin.cast_refl] using hl vertex

 theorem vertex_cast (security : ℕ) (vertex : Fin (Size security)) :
    CurrentAffineGeometry.dimensionEquiv security
      (vertex.cast (congrArg (fun n => n + 1) (current_values security).2.1)) = vertexEquiv security vertex := by
  apply Fin.ext
  rfl

 theorem permuted_column_load (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (core : MaterializedCore security) (scale shear : Vector IntegerBits (Legs security))
    (column row : Fin (Size security)) :
    ((binaryPermutedColumn (current security).edges
      (CurrentBinaryLoadColumns.matrix security scale shear (CurrentEmissionRootOrder.positions security layout core).value).value
      (endpointPermutation security core).value column).value.get row).decode =
    CurrentAffineEmissionBridge.linearLoad security layout.layout core.core
      (fun leg => (scale.get ((legEquiv security).symm leg)).decode)
      (fun leg => (shear.get ((legEquiv security).symm leg)).decode)
      (CurrentBinaryLoadSemantic.basisInput security column) (vertexEquiv security row) := by
  rw [binaryPermutedColumn_value, CurrentBinaryLoadColumns.matrix_value, CurrentBinaryLoadSemantic.loadEntry_eq]
  have hp := numbering_point security ((physicalVertexNumberingProgram (Legs security) (current security).rest
    (current security).edges (current_counts security).2.2.2.1).symm ((endpointPermutation security core).value.get row))
  rw [Equiv.apply_symm_apply] at hp
  rw [← hp, endpointPermutation_value, Equiv.symm_apply_apply]

 theorem column_value (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (core : MaterializedCore security) (scale shear : Vector IntegerBits (Legs security))
    (column : Fin (Size security)) :
    CurrentBinaryAffineEmitter.decodeCoordinate security
      (binaryAffineColumn (current security).edges
        (canonicalCounter (PublicParameterProgram.modulus security).count).digits
        (injection security).value
        (CurrentBinaryLoadColumns.matrix security scale shear (CurrentEmissionRootOrder.positions security layout core).value).value
        (endpointPermutation security core).value column).value =
    fun row => CurrentAffineGeometry.matrix security layout.layout core.core
      (fun leg => (scale.get ((legEquiv security).symm leg)).decode)
      (fun leg => (shear.get ((legEquiv security).symm leg)).decode) row (vertexEquiv security column) := by
  unfold CurrentBinaryAffineEmitter.decodeCoordinate binaryAffineColumn
  apply native_inverse_eq security layout.layout (current security).edges (current_values security).2.1
  · rw [canonicalCounter_value, PublicParameterProgram.modulus_value]
  · intro vertex
    exact injection_value security vertex
  · intro vertex
    rw [permuted_column_load, vertex_cast]
    exact congrFun (CurrentAffineEmissionBridge.matrix_column_rounding security layout.layout core.core _ _
      (vertexEquiv security column)).symm (vertexEquiv security vertex)

 theorem assembled_matrix (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security) :
    CurrentBinaryAffineEmitter.matrix security (CurrentBinaryAffineEmitter.assembled security layout sample) =
      CurrentAffineGeometry.matrix security layout.layout sample.core.core
        (CurrentAffineData.scales security sample.charts.get) (CurrentAffineData.shears security sample.charts.get) := by
  funext row column
  simp only [CurrentBinaryAffineEmitter.matrix, CurrentBinaryAffineEmitter.assembled, storeData_get, column_value,
    Equiv.apply_symm_apply]
  congr 1 <;> funext leg <;>
    simp only [CurrentBinaryChartData.fieldArray_value, Equiv.apply_symm_apply,
      CurrentAffineData.scales, CurrentAffineData.shears]

end
end CurrentAFT.CurrentBinaryMatrixSemantic

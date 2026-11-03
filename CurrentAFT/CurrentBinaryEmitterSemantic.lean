import CurrentAFT.CurrentBinaryMatrixSemantic
import CurrentAFT.CurrentBinaryOffsetSemantic

/-! The complete executable emitter has exactly the current public affine
semantics, including both validity failures and the absent-result fallback. -/
namespace CurrentAFT.CurrentBinaryEmitterSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section

 theorem permuted_offset_load (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security) (hcharge : ActualPublicCharge.publicCharge security sample.core.core)
    (row : Fin (Size security)) :
    ((permuteLoad security
      (CurrentBinaryOffsetLoad.load security sample.core
        ⟨false, (canonicalCounter (PublicParameterProgram.modulus security).count).digits⟩
        (CurrentBinaryChartData.shiftArray security sample.core).value
        (CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.1)).value
        (CurrentEmissionRootOrder.positions security layout sample.core).value
        (CurrentPublicShiftProgram.encode sample.edge.val).value).value
      (endpointPermutation security sample.core).value).value.get row).decode =
    CurrentAffineLoad.rounding security
      (CurrentAffineGeometry.offset security layout.layout sample.core.core
        (CurrentAffineData.intercepts security sample.charts.get) sample.edge.val hcharge) (vertexEquiv security row) := by
  rw [permuteLoad_value, CurrentBinaryOffsetLoad.load_value security sample.core layout.layout]
  have hmod : (⟨false, (canonicalCounter (PublicParameterProgram.modulus security).count).digits⟩ : IntegerBits).decode = Parameters.modulus security := by
    simp only [IntegerBits.decode, signedValue, canonicalCounter_value, PublicParameterProgram.modulus_value, Bool.false_eq_true, if_false]
  rw [hmod, CurrentPublicShiftProgram.encode_value]
  simp only [CurrentBinaryChartData.shiftArray_value]
  rw [CurrentBinaryOffsetSemantic.physicalLoad_eq security layout sample.core _ _ hcharge]
  have hp := numbering_point security ((physicalVertexNumberingProgram (Legs security) (current security).rest
    (current security).edges (current_counts security).2.2.2.1).symm ((endpointPermutation security sample.core).value.get row))
  rw [Equiv.apply_symm_apply] at hp
  rw [← hp, endpointPermutation_value, Equiv.symm_apply_apply]
  congr 2
  funext leg
  simp only [CurrentBinaryChartData.fieldArray_value, Equiv.apply_symm_apply, CurrentAffineData.intercepts]

 theorem assembled_offset (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security) (hcharge : ActualPublicCharge.publicCharge security sample.core.core) :
    CurrentBinaryAffineEmitter.offset security (CurrentBinaryAffineEmitter.assembled security layout sample) =
      CurrentAffineGeometry.offset security layout.layout sample.core.core
        (CurrentAffineData.intercepts security sample.charts.get) sample.edge.val hcharge := by
  unfold CurrentBinaryAffineEmitter.offset CurrentBinaryAffineEmitter.assembled CurrentBinaryAffineEmitter.decodeCoordinate
  apply CurrentBinaryMatrixSemantic.native_inverse_eq security layout.layout (current security).edges (current_values security).2.1
  · rw [canonicalCounter_value, PublicParameterProgram.modulus_value]
  · intro vertex
    exact injection_value security vertex
  · intro vertex
    rw [permuted_offset_load security layout sample hcharge, CurrentBinaryMatrixSemantic.vertex_cast]

 theorem emit_matrix (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (input : Option (CurrentMaterializedCompletion.Result security)) :
    CurrentBinaryAffineEmitter.matrix security (CurrentBinaryAffineEmitter.emit security layout input) =
      (NumericalAffineTransport.realizeResult security layout.layout (input.map CurrentMaterializedCompletion.Result.sample)).matrix := by
  cases input with
  | none => exact CurrentBinaryFallbackSemantic.matrix_value security
  | some sample =>
    by_cases h : CurrentAffineData.Valid security sample.core.core sample.charts.get
    · have he := (CurrentBinaryAffineEmitter.emit_valid security layout sample h).1
      change (fun row column => CurrentBinaryAffineEmitter.decodeCoordinate security
        ((CurrentBinaryAffineEmitter.emit security layout (some sample)).columns.get ((vertexEquiv security).symm column)) row) = _
      rw [he]
      exact (CurrentBinaryMatrixSemantic.assembled_matrix security layout sample).trans (by
        simp only [NumericalAffineTransport.realizeResult, Option.map_some, CurrentPublicAffineSample.realize,
          CurrentMaterializedCompletion.Result.sample, CurrentAffineData.assemble, dif_pos h, CurrentAffineData.assembled])
    · have he := (CurrentBinaryAffineEmitter.emit_invalid security layout sample h).1
      change (fun row column => CurrentBinaryAffineEmitter.decodeCoordinate security
        ((CurrentBinaryAffineEmitter.emit security layout (some sample)).columns.get ((vertexEquiv security).symm column)) row) = _
      rw [he]
      exact (CurrentBinaryFallbackSemantic.matrix_value security).trans (by
        simp only [NumericalAffineTransport.realizeResult, Option.map_some, CurrentPublicAffineSample.realize,
          CurrentMaterializedCompletion.Result.sample, CurrentAffineData.assemble, dif_neg h, CurrentAffineData.fallback])

 theorem emit_offset (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (input : Option (CurrentMaterializedCompletion.Result security)) :
    CurrentBinaryAffineEmitter.offset security (CurrentBinaryAffineEmitter.emit security layout input) =
      (NumericalAffineTransport.realizeResult security layout.layout (input.map CurrentMaterializedCompletion.Result.sample)).offset := by
  cases input with
  | none => exact CurrentBinaryFallbackSemantic.offset_value security
  | some sample =>
    by_cases h : CurrentAffineData.Valid security sample.core.core sample.charts.get
    · have he := (CurrentBinaryAffineEmitter.emit_valid security layout sample h).2
      change CurrentBinaryAffineEmitter.decodeCoordinate security (CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = _
      rw [he]
      exact (assembled_offset security layout sample h.1).trans (by
        simp only [NumericalAffineTransport.realizeResult, Option.map_some, CurrentPublicAffineSample.realize,
          CurrentMaterializedCompletion.Result.sample, CurrentAffineData.assemble, dif_pos h, CurrentAffineData.assembled])
    · have he := (CurrentBinaryAffineEmitter.emit_invalid security layout sample h).2
      change CurrentBinaryAffineEmitter.decodeCoordinate security (CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = _
      rw [he]
      exact (CurrentBinaryFallbackSemantic.offset_value security).trans (by
        simp only [NumericalAffineTransport.realizeResult, Option.map_some, CurrentPublicAffineSample.realize,
          CurrentMaterializedCompletion.Result.sample, CurrentAffineData.assemble, dif_neg h, CurrentAffineData.fallback])

end
end CurrentAFT.CurrentBinaryEmitterSemantic

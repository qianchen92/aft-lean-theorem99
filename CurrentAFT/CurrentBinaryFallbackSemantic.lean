import CurrentAFT.CurrentBinaryAffineEmitter

/-! Every invalid or absent sample emits the same integer identity fallback
as the analytic affine constructor. -/
namespace CurrentAFT.CurrentBinaryFallbackSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentBinaryAffineEmitter
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

private theorem hit_value (test : Prop) [Decidable test] : (if test then IntegerBits.one else IntegerBits.zero).decode = if test then 1 else 0 := by
  split_ifs <;> rfl

 theorem column_value (security : ℕ) (column : Fin (CurrentBinaryAffinePrimitives.Size security)) :
    CurrentBinaryAffineEmitter.decodeCoordinate security (fallbackColumn security column).value = Pi.single (vertexEquiv security column) 1 := by
  funext row
  obtain ⟨edge | point, rfl⟩ := (CurrentAffineGeometry.coordinateNumbering security).surjective row
  · have he : (equalCounter edge.val column.val).value = true ↔
        CurrentAffineGeometry.coordinateNumbering security (.inl edge) = vertexEquiv security column := by
      rw [equalCounter_value, Fin.ext_iff]
      change edge.val = column.val ↔ edge.val = column.val
      rfl
    simp only [CurrentBinaryAffineEmitter.decodeCoordinate, CurrentAffineLoad.packSource, Equiv.symm_apply_apply, Sum.elim_inl,
      fallbackColumn, storeData_get, Fin.val_cast, hit_value, Pi.single_apply, he]
  · cases point
    have he : (equalCounter column.val (current security).edges).value = true ↔
        CurrentAffineGeometry.coordinateNumbering security (.inr ()) = vertexEquiv security column := by
      rw [equalCounter_value, Fin.ext_iff]
      change column.val = (current security).edges ↔ CurrentAffineGeometry.edgeCount security = column.val
      rw [(current_values security).2.1]
      exact eq_comm
    simp only [CurrentBinaryAffineEmitter.decodeCoordinate, CurrentAffineLoad.packSource, Equiv.symm_apply_apply, Sum.elim_inr,
      fallbackColumn, hit_value, Pi.single_apply, he]

 theorem matrix_value (security : ℕ) : CurrentBinaryAffineEmitter.matrix security (fallback security) = 1 := by
  funext row column
  change CurrentBinaryAffineEmitter.decodeCoordinate security ((storeData _ (fallbackColumn security)).value.get ((vertexEquiv security).symm column)) row = _
  rw [storeData_get, column_value, Equiv.apply_symm_apply]
  simp [Pi.single_apply, Matrix.one_apply]

 theorem offset_value (security : ℕ) : CurrentBinaryAffineEmitter.offset security (fallback security) = 0 := by
  funext row
  obtain ⟨edge | point, rfl⟩ := (CurrentAffineGeometry.coordinateNumbering security).surjective row
  · simp only [offset, fallback, CurrentBinaryAffineEmitter.decodeCoordinate, CurrentAffineLoad.packSource, Equiv.symm_apply_apply,
      Sum.elim_inl, storeData_get, IntegerBits.zero_value, Pi.zero_apply]
  · cases point
    simp only [offset, fallback, CurrentBinaryAffineEmitter.decodeCoordinate, CurrentAffineLoad.packSource, Equiv.symm_apply_apply,
      Sum.elim_inr, IntegerBits.zero_value, Pi.zero_apply]

end CurrentAFT.CurrentBinaryFallbackSemantic

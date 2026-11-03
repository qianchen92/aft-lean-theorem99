import CurrentAFT.BinaryFullResponseMatrixEntryProgram
import CurrentAFT.BinaryFullResponseSemantic

namespace CurrentAFT.BinaryFullResponseMatrixEntry
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFullResponseData BinaryRectangleMaterialization
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local irreducible] PublicParameterProgram.modulus BinaryFullResponseProgram.current BinaryNaturalCoordinates.current
  RationalFullResponseProgram.defect

theorem validEntry_value (security bits order : ℕ) (data : Data order) (hdata : Correct data)
    (output source : CurrentBinaryRectangleDecode.Data security order) :
    (validEntry security bits order data output source).value.decode=
      RationalFullResponseProgram.matrix security bits order
        (CurrentBinaryRectangleDecode.semanticPoint security order output) (CurrentBinaryRectangleDecode.semanticPoint security order source) := by
  have h := BinaryFullResponseProgram.current_value security bits order data hdata source.arity source.primary source.body output.arity
    (BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.primary).value
    (BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.body).value
    (BinaryNaturalCoordinates.current_valid _ _) (BinaryNaturalCoordinates.current_valid _ _)
  have hp : (BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.primary).value.get=
      fun index => (output.primary.get index).val := by
    funext index
    exact BinaryNaturalCoordinates.current_get _ _ index
  have hb : (BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.body).value.get=
      fun index => (output.body.get index).val := by
    funext index
    exact BinaryNaturalCoordinates.current_get _ _ index
  rw [hp,hb] at h
  simpa only [validEntry,BinaryNaturalCoordinates.current_get,RationalFullResponseProgram.matrix,
    CurrentBinaryRectangleDecode.semanticPoint_arity,CurrentBinaryRectangleDecode.semanticPoint_primary_value,
    CurrentBinaryRectangleDecode.semanticPoint_body_value] using h

theorem current_value (security bits order : ℕ) (data : Data order) (hdata : Correct data)
    (output source : Fin (Size security order)) :
    (current security bits order data output source).value.decode=
      CurrentRectangleIndex.defect security order (RationalFullResponseProgram.matrix security bits order)
        (finProdFinEquiv.symm output) (finProdFinEquiv.symm source) :=
  BinaryRectangleEntry.current_value security order (validEntry security bits order data)
    (RationalFullResponseProgram.matrix security bits order) (validEntry_value security bits order data hdata) output source


end
end CurrentAFT.BinaryFullResponseMatrixEntry

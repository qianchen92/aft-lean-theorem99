import CurrentAFT.CurrentCoreProposal
import CurrentAFT.CurrentAffineData
import CurrentAFT.CurrentEmissionMetadata
import CurrentAFT.CurrentPublicShiftCost

/-! Materialization of actual chart scalars and public leg shifts. Every chart
and public input is read from its stored vector; no chart-function oracle is used. -/
namespace CurrentAFT.CurrentBinaryChartData
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

abbrev Charts (security : ℕ) := Vector (CurrentAffineLegCarry.PublicChart security) (Parameters.legCount security)

def defaultChart (security : ℕ) : CurrentAffineLegCarry.PublicChart security := (false, 0, 0, 0)

def fieldArray (security : ℕ) (charts : Charts security)
    (field : CurrentAffineLegCarry.PublicChart security → ZMod (Parameters.modulus security)) :
    CountedValue (Vector IntegerBits (CurrentProposalDimensions.current security).legs) :=
  storeData (CurrentProposalDimensions.current security).legs (fun leg =>
    let chart := readVector (defaultChart security) charts (legEquiv security leg)
    let encoded := CurrentPublicShiftProgram.encode (field chart.value).val
    ⟨encoded.value, chart.work + encoded.work + 2⟩)

theorem fieldArray_value (security : ℕ) (charts : Charts security)
    (field : CurrentAffineLegCarry.PublicChart security → ZMod (Parameters.modulus security))
    (leg : Fin (CurrentProposalDimensions.current security).legs) :
    ((fieldArray security charts field).value.get leg).decode = (field (charts.get (legEquiv security leg))).val := by
  simp only [fieldArray, storeData_get, CurrentPublicShiftProgram.encode_value, readVector_value]

theorem fieldArray_length (security : ℕ) (charts : Charts security)
    (field : CurrentAffineLegCarry.PublicChart security → ZMod (Parameters.modulus security))
    (leg : Fin (CurrentProposalDimensions.current security).legs) :
    ((fieldArray security charts field).value.get leg).digits.length ≤ Parameters.modulus security := by
  rw [show (fieldArray security charts field).value.get leg =
    (CurrentPublicShiftProgram.encode (field (charts.get (legEquiv security leg))).val).value by
      simp only [fieldArray, storeData_get, readVector_value]]
  apply (CurrentPublicShiftProgram.encode_length _).trans
  rw [Int.natAbs_natCast]
  exact (ZMod.val_lt _).le

theorem fieldArray_work (security : ℕ) (charts : Charts security)
    (field : CurrentAffineLegCarry.PublicChart security → ZMod (Parameters.modulus security)) :
    (fieldArray security charts field).work ≤ (CurrentProposalDimensions.current security).legs *
      (3 * Parameters.legCount security + 50 * (Parameters.modulus security + 1)^2 + 10) + 2 := by
  apply storeData_work
  intro leg
  have hr := readVector_work (defaultChart security) charts (legEquiv security leg)
  have he := CurrentPublicShiftProgram.encode_work (field (readVector (defaultChart security) charts (legEquiv security leg)).value).val
  have hv : ((field (readVector (defaultChart security) charts (legEquiv security leg)).value).val : ℤ).natAbs ≤ Parameters.modulus security := by
    rw [Int.natAbs_natCast]
    exact (ZMod.val_lt _).le
  have hm : 50 * (((field (readVector (defaultChart security) charts (legEquiv security leg)).value).val : ℤ).natAbs + 1)^2 ≤
      50 * (Parameters.modulus security + 1)^2 := by gcongr
  change (readVector (defaultChart security) charts (legEquiv security leg)).work +
    (CurrentPublicShiftProgram.encode _).work + 2 ≤ _
  omega


def shiftArray (security : ℕ) (core : MaterializedCore security) :
    CountedValue (Vector IntegerBits (CurrentProposalDimensions.current security).legs) :=
  storeData (CurrentProposalDimensions.current security).legs (fun leg =>
    let input := readVector (CurrentChartsDraw.defaultInput security) core.inputs (legEquiv security leg)
    let shifted := CurrentPublicShiftProgram.current security input.value.1 input.value.2
    ⟨shifted.value, input.work + shifted.work + 2⟩)

theorem shiftArray_value (security : ℕ) (core : MaterializedCore security)
    (leg : Fin (CurrentProposalDimensions.current security).legs) :
    ((shiftArray security core).value.get leg).decode = ActualPublicCharge.legShift security core.core (legEquiv security leg) := by
  simp only [shiftArray, storeData_get, CurrentPublicShiftProgram.current_value, readVector_value,
    core.inputs_correct, ActualPublicCharge.legShift, MaterializedCore.core, decode]

theorem shiftArray_work (security : ℕ) (core : MaterializedCore security) :
    (shiftArray security core).work ≤ (CurrentProposalDimensions.current security).legs *
      (3 * Parameters.legCount security + CurrentPublicShiftProgram.workBound security + 9) + 2 := by
  apply storeData_work
  intro leg
  have hr := readVector_work (CurrentChartsDraw.defaultInput security) core.inputs (legEquiv security leg)
  have hs := CurrentPublicShiftProgram.current_work security
    (readVector (CurrentChartsDraw.defaultInput security) core.inputs (legEquiv security leg)).value.1
    (readVector (CurrentChartsDraw.defaultInput security) core.inputs (legEquiv security leg)).value.2
  change (readVector (CurrentChartsDraw.defaultInput security) core.inputs (legEquiv security leg)).work +
    (CurrentPublicShiftProgram.current security _ _).work + 2 ≤ _
  omega

end CurrentAFT.CurrentBinaryChartData

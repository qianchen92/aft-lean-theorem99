import CurrentAFT.CurrentBinaryOffsetLoad
import CurrentAFT.BinaryCoreCharge
import AFT.BinaryAffineAssembly

/-! The current fixed rounding injection and the stored final endpoint
permutation are produced by charged comparisons and vector reads. -/
namespace CurrentAFT.CurrentBinaryAffinePrimitives
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Size (security : ℕ) := (current security).edges + 1


def injection (security : ℕ) : CountedValue (Vector IntegerBits (Size security)) :=
  storeData (Size security) (fun row =>
    let hit := lessCounter row.val (CurrentProposalDimensions.current security).colors
    ⟨if hit.value then IntegerBits.one else IntegerBits.zero, hit.work + 2⟩)

 theorem injection_value (security : ℕ) (row : Fin (Size security)) :
    ((injection security).value.get row).decode = injectionColumn (current security).edges (Parameters.modulus security) row := by
  have h : (lessCounter row.val (CurrentProposalDimensions.current security).colors).value = true ↔ row.val < Parameters.modulus security := by
    rw [lessCounter_value, (CurrentProposalDimensions.current_values security).1]
  simp only [injection, storeData_get, injectionColumn]
  by_cases ht : (lessCounter row.val (CurrentProposalDimensions.current security).colors).value = true
  · rw [if_pos ht, if_pos (h.mp ht), IntegerBits.one_value]
  · rw [if_neg ht, if_neg (fun hh => ht (h.mpr hh)), IntegerBits.zero_value]

 theorem injection_length (security : ℕ) (row : Fin (Size security)) :
    ((injection security).value.get row).digits.length ≤ 1 := by
  simp only [injection, storeData_get]
  split_ifs <;> decide

 theorem injection_work (security : ℕ) : (injection security).work ≤
    Size security * (3 * Size security + 7) + 2 := by
  apply storeData_work
  intro row
  have h := lessCounter_work_left row.val (CurrentProposalDimensions.current security).colors
  change (lessCounter row.val (CurrentProposalDimensions.current security).colors).work + 2 ≤ _
  have hi := row.isLt
  omega


def endpointPermutation (security : ℕ) (core : MaterializedCore security) :
    CountedValue (Vector (Fin (Size security)) (Size security)) :=
  storeData (Size security) (fun row =>
    let index := row.cast (current_counts security).2.1
    let selected := readVector index core.endpoints.forward index
    ⟨selected.value.cast (current_counts security).2.1.symm, selected.work + 2⟩)

 theorem endpointPermutation_value (security : ℕ) (core : MaterializedCore security) (row : Fin (Size security)) :
    vertexEquiv security ((endpointPermutation security core).value.get row) =
      core.core.endpointPermutation (vertexEquiv security row) := by
  simp only [endpointPermutation, storeData_get, readVector_value, MaterializedCore.core, decode,
    Equiv.permCongr_apply]
  apply Fin.ext
  change (core.endpoints.forward.get (row.cast (current_counts security).2.1)).val =
    (core.endpoints.forward.get ((CurrentProposalDimensions.endpointEquiv security).symm (vertexEquiv security row))).val
  have hi : row.cast (current_counts security).2.1 =
      (CurrentProposalDimensions.endpointEquiv security).symm (vertexEquiv security row) := by
    apply Fin.ext
    rfl
  rw [hi]

 theorem endpointPermutation_work (security : ℕ) (core : MaterializedCore security) :
    (endpointPermutation security core).work ≤ Size security * (3 * Size security + 7) + 2 := by
  apply storeData_work
  intro row
  have h := readVector_work (row.cast (current_counts security).2.1) core.endpoints.forward
    (row.cast (current_counts security).2.1)
  change (readVector (row.cast (current_counts security).2.1) core.endpoints.forward _).work + 2 ≤ _
  have hc : (CurrentProposalDimensions.current security).dimension = Size security := (current_counts security).2.1.symm
  omega


def permuteLoad (security : ℕ) (data : Vector IntegerBits (Size security))
    (permutation : Vector (Fin (Size security)) (Size security)) : CountedValue (Vector IntegerBits (Size security)) :=
  storeData (Size security) (fun row =>
    let position := readVector 0 permutation row
    let selected := readVector IntegerBits.zero data position.value
    ⟨selected.value, position.work + selected.work + 2⟩)

 theorem permuteLoad_value (security : ℕ) (data : Vector IntegerBits (Size security))
    (permutation : Vector (Fin (Size security)) (Size security)) (row : Fin (Size security)) :
    (permuteLoad security data permutation).value.get row = data.get (permutation.get row) := by
  simp only [permuteLoad, storeData_get, readVector_value]

 theorem permuteLoad_work (security : ℕ) (data : Vector IntegerBits (Size security))
    (permutation : Vector (Fin (Size security)) (Size security)) :
    (permuteLoad security data permutation).work ≤ Size security * (6 * Size security + 10) + 2 := by
  apply storeData_work
  intro row
  have hp := readVector_work 0 permutation row
  have hd := readVector_work IntegerBits.zero data (readVector 0 permutation row).value
  change (readVector 0 permutation row).work + (readVector IntegerBits.zero data _).work + 2 ≤ _
  omega

end CurrentAFT.CurrentBinaryAffinePrimitives

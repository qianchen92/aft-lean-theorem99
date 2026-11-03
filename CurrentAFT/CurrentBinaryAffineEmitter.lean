import CurrentAFT.CurrentBinaryAffineGuard
import CurrentAFT.CurrentMaterializedCompletion
import CurrentAFT.CurrentAffineEmissionBridge

/-! The executed integer affine emitter. It consumes only stored public
buffers. All legal columns and the offset are computed by binary rounding
inversion, while failed validity and absent samples emit the integer identity. -/
namespace CurrentAFT.CurrentBinaryAffineEmitter
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
open CurrentBinaryAffinePrimitives CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Data (security : ℕ) := BinaryAffineData (CurrentEmissionMetadata.current security).edges
abbrev Coordinate (security : ℕ) := Vector IntegerBits (CurrentEmissionMetadata.current security).edges × IntegerBits


def fallbackColumn (security : ℕ) (column : Fin (Size security)) : CountedValue (Coordinate security) :=
  let edges := storeData (CurrentEmissionMetadata.current security).edges (fun row =>
    let equal := equalCounter row.val column.val
    ⟨if equal.value then IntegerBits.one else IntegerBits.zero, equal.work + 2⟩)
  let chargeHit := equalCounter column.val (CurrentEmissionMetadata.current security).edges
  ⟨(edges.value, if chargeHit.value then IntegerBits.one else IntegerBits.zero), edges.work + chargeHit.work + 3⟩


def fallback (security : ℕ) : Data security :=
  let metadata := CurrentEmissionMetadata.current security
  let columns := storeData (Size security) (fallbackColumn security)
  let offset := storeData metadata.edges (fun _ => ⟨IntegerBits.zero, 1⟩)
  ⟨columns.value, (offset.value, IntegerBits.zero), metadata.work + columns.work + offset.work + 3⟩


def assembled (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security) : Data security :=
  let metadata := CurrentEmissionMetadata.current security
  let q := PublicParameterProgram.modulus security
  let qbits := canonicalCounter q.count
  let modulus : IntegerBits := ⟨false, qbits.digits⟩
  let scale := CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.2.1)
  let shear := CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.2.2)
  let intercept := CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.1)
  let shift := CurrentBinaryChartData.shiftArray security sample.core
  let closure := CurrentPublicShiftProgram.encode sample.edge.val
  let roots := CurrentEmissionRootOrder.positions security layout sample.core
  let matrix := CurrentBinaryLoadColumns.matrix security scale.value shear.value roots.value
  let initial := CurrentBinaryOffsetLoad.load security sample.core modulus shift.value intercept.value roots.value closure.value
  let injection := CurrentBinaryAffinePrimitives.injection security
  let permutation := CurrentBinaryAffinePrimitives.endpointPermutation security sample.core
  let columns := storeData (Size security) (binaryAffineColumn metadata.edges qbits.digits injection.value matrix.value permutation.value)
  let offsetLoad := CurrentBinaryAffinePrimitives.permuteLoad security initial.value permutation.value
  let offset := binaryRoundingInverse metadata.edges qbits.digits injection.value offsetLoad.value
  ⟨columns.value, (offset.edges, offset.charge),
    metadata.work + q.work + qbits.work + scale.work + shear.work + intercept.work + shift.work + closure.work +
      roots.work + matrix.work + initial.work + injection.work + permutation.work + columns.work + offsetLoad.work + offset.work + 16⟩


def emit (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (input : Option (CurrentMaterializedCompletion.Result security)) : Data security :=
  match input with
  | none => fallback security
  | some sample =>
    let tested := CurrentBinaryAffineGuard.current security sample.core sample.charts
    let result := if tested.value then assembled security layout sample else fallback security
    ⟨result.columns, result.offset, tested.work + result.work + 2⟩

noncomputable section

def decodeCoordinate (security : ℕ) (point : Coordinate security) : Fin (Parameters.dimension security) → ℤ :=
  CurrentAffineLoad.packSource security
    ((fun edge => (point.1.get (edge.cast (CurrentEmissionMetadata.current_values security).2.1.symm)).decode), point.2.decode)


def matrix (security : ℕ) (data : Data security) : Matrix (Fin (Parameters.dimension security)) (Fin (Parameters.dimension security)) ℤ :=
  fun row column => decodeCoordinate security (data.columns.get ((vertexEquiv security).symm column)) row


def offset (security : ℕ) (data : Data security) : Fin (Parameters.dimension security) → ℤ :=
  decodeCoordinate security data.offset

 theorem emit_none (security : ℕ) (layout : CurrentLayoutDraw.Cache security) : emit security layout none = fallback security := rfl

 theorem emit_invalid (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security)
    (h : ¬CurrentAffineData.Valid security sample.core.core sample.charts.get) :
    (emit security layout (some sample)).columns = (fallback security).columns ∧
      (emit security layout (some sample)).offset = (fallback security).offset := by
  have ht : ¬(CurrentBinaryAffineGuard.current security sample.core sample.charts).value = true :=
    fun ht => h ((CurrentBinaryAffineGuard.current_value security sample.core sample.charts).mp ht)
  simp only [emit, if_neg ht, and_self]

 theorem emit_valid (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security)
    (h : CurrentAffineData.Valid security sample.core.core sample.charts.get) :
    (emit security layout (some sample)).columns = (assembled security layout sample).columns ∧
      (emit security layout (some sample)).offset = (assembled security layout sample).offset := by
  have ht := (CurrentBinaryAffineGuard.current_value security sample.core sample.charts).mpr h
  simp only [emit, if_pos ht, and_self]

end
end CurrentAFT.CurrentBinaryAffineEmitter

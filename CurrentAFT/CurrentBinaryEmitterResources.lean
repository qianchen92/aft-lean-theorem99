import CurrentAFT.CurrentBinaryAffineEmitter
import CurrentAFT.CurrentBinaryLoadResources
import CurrentAFT.CurrentBinaryOffsetResources
import CurrentAFT.BinaryCoreChargeResources
import AFT.BinaryAffinePolynomial

/-! Explicit work bounds for the current stored-buffer integer emitter. -/
namespace CurrentAFT.CurrentBinaryEmitterResources
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentProposalResources
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount


def operandBits (security : ℕ) : ℕ := Parameters.modulus security + 2*(security+2)^48 + 2*(security+2)^2 + 10

def fieldWork (security : ℕ) : ℕ := Legs security * (3*Parameters.legCount security + 50*(Parameters.modulus security+1)^2 + 10)+2

def shiftWork (security : ℕ) : ℕ := Legs security * (3*Parameters.legCount security + CurrentPublicShiftProgram.workBound security + 9)+2


def assembledWork (security : ℕ) : ℕ :=
  let e := (current security).edges
  let size := e+1
  let body := (CurrentProposalDimensions.current security).body
  let bits := operandBits security
  (current security).work + PublicParameterProgram.workBound security + 50*(Parameters.modulus security+1)^2 +
    3*fieldWork security + shiftWork security + (50*((security+2)^2+1)^2+1) +
    (body*(13*body+19)+2) + CurrentBinaryLoadResources.matrixWork security bits +
    CurrentBinaryOffsetResources.loadWork security bits + (size*(3*size+7)+2) + (size*(3*size+7)+2) +
    (size*((size*(9*size+15)+2)+binaryRoundingInverseWork e (Parameters.modulus security) (bits+3)+4)+2) +
    (size*(6*size+10)+2) + binaryRoundingInverseWork e (Parameters.modulus security) (bits+3) + 16

 theorem assembled_work (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security) :
    (CurrentBinaryAffineEmitter.assembled security layout sample).work ≤ assembledWork security := by
  let metadata := current security
  let q := PublicParameterProgram.modulus security
  let qbits := canonicalCounter q.count
  let modulus : IntegerBits := ⟨false,qbits.digits⟩
  let scales := CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.2.1)
  let shears := CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.2.2)
  let intercept := CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.1)
  let shift := CurrentBinaryChartData.shiftArray security sample.core
  let closure := CurrentPublicShiftProgram.encode sample.edge.val
  let roots := CurrentEmissionRootOrder.positions security layout sample.core
  let matrix := CurrentBinaryLoadColumns.matrix security scales.value shears.value roots.value
  let initial := CurrentBinaryOffsetLoad.load security sample.core modulus shift.value intercept.value roots.value closure.value
  let inj := injection security
  let perm := endpointPermutation security sample.core
  let columns := storeData (Size security) (binaryAffineColumn metadata.edges qbits.digits inj.value matrix.value perm.value)
  let offsetLoad := permuteLoad security initial.value perm.value
  let inverse := binaryRoundingInverse metadata.edges qbits.digits inj.value offsetLoad.value
  let bits := operandBits security
  have hbits : 1 ≤ bits := by dsimp only [bits,operandBits]; omega
  have hq : Parameters.modulus security ≤ bits := by dsimp only [bits,operandBits]; omega
  have hs : ∀ leg, (scales.value.get leg).digits.length ≤ bits := fun leg =>
    (CurrentBinaryChartData.fieldArray_length security sample.charts _ leg).trans hq
  have hh : ∀ leg, (shears.value.get leg).digits.length ≤ bits := fun leg =>
    (CurrentBinaryChartData.fieldArray_length security sample.charts _ leg).trans hq
  have hi : ∀ leg, (intercept.value.get leg).digits.length ≤ bits := fun leg =>
    (CurrentBinaryChartData.fieldArray_length security sample.charts _ leg).trans hq
  have ht : ∀ leg, (shift.value.get leg).digits.length ≤ bits := by
    intro leg
    have ht := CurrentPublicShiftProgram.current_length security
      (readVector (CurrentChartsDraw.defaultInput security) sample.core.inputs (legEquiv security leg)).value.1
      (readVector (CurrentChartsDraw.defaultInput security) sample.core.inputs (legEquiv security leg)).value.2
    have htl : (shift.value.get leg).digits.length ≤ 2*(security+2)^48+2*(security+2)^2+2 := by
      simpa only [shift, CurrentBinaryChartData.shiftArray, storeData_get] using ht
    dsimp only [bits,operandBits]
    omega
  have hcl : closure.value.digits.length ≤ bits := by
    have he := (CurrentPublicShiftProgram.encode_length sample.edge.val).trans (CurrentPublicShiftProgram.edge_size security sample.edge)
    change closure.value.digits.length ≤ _ at he
    dsimp only [bits,operandBits]
    omega
  have hqbit : qbits.digits.length ≤ Parameters.modulus security := by
    rw [show qbits.digits.length = Nat.size (Parameters.modulus security) by
      simp only [qbits,q,canonicalCounter_length,PublicParameterProgram.modulus_value]]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := _))
  have hm : modulus.digits.length ≤ bits := hqbit.trans hq
  have hmx := CurrentBinaryLoadResources.matrix_work security bits scales.value shears.value roots.value hs hh
  have hml := CurrentBinaryLoadResources.matrix_length security bits hbits scales.value shears.value roots.value hs hh
  have hinit := CurrentBinaryOffsetResources.load_work security bits hbits sample.core modulus shift.value intercept.value roots.value closure.value hm ht hi hcl
  have hil := CurrentBinaryOffsetResources.load_length security bits hbits hq sample.core modulus shift.value intercept.value roots.value closure.value hm ht hi hcl
  have hinj : ∀ row, (inj.value.get row).digits.length ≤ bits+3 := fun row => (injection_length security row).trans (by omega)
  have hc (column : Fin (Size security)) : (binaryAffineColumn metadata.edges qbits.digits inj.value matrix.value perm.value column).work ≤
      (Size security*(9*Size security+15)+2)+binaryRoundingInverseWork metadata.edges (Parameters.modulus security) (bits+3)+2 := by
    have hp := binaryPermutedColumn_work metadata.edges matrix.value perm.value column
    have hv := binaryRoundingInverse_work metadata.edges (bits+3) qbits.digits inj.value
      (binaryPermutedColumn metadata.edges matrix.value perm.value column).value hinj (fun row => by
        rw [binaryPermutedColumn_value]; exact hml column (perm.value.get row))
    have hv' := hv.trans (binaryRoundingInverseWork_mono le_rfl hqbit le_rfl)
    change (binaryPermutedColumn metadata.edges matrix.value perm.value column).work ≤
      Size security*(9*Size security+15)+2 at hp
    change (binaryPermutedColumn _ _ _ _).work + (binaryRoundingInverse _ _ _ _).work + 2 ≤ _
    omega
  have hcwork := storeData_work (Size security) _ _ hc
  have ho := binaryRoundingInverse_work metadata.edges (bits+3) qbits.digits inj.value offsetLoad.value hinj (fun row => by
    rw [permuteLoad_value]; exact hil (perm.value.get row))
  have ho' := ho.trans (binaryRoundingInverseWork_mono le_rfl hqbit le_rfl)
  have hp := permuteLoad_work security initial.value perm.value
  have hqs := PublicParameterProgram.modulus_work security
  have hqw : qbits.work ≤ 50*(Parameters.modulus security+1)^2 := by
    apply (canonicalCounter_work q.count).trans
    rw [PublicParameterProgram.modulus_value]
  have hsc := CurrentBinaryChartData.fieldArray_work security sample.charts (fun chart => chart.2.2.1)
  have hsh := CurrentBinaryChartData.fieldArray_work security sample.charts (fun chart => chart.2.2.2)
  have hiv := CurrentBinaryChartData.fieldArray_work security sample.charts (fun chart => chart.2.1)
  have hsw := CurrentBinaryChartData.shiftArray_work security sample.core
  have hcw : closure.work ≤ 50*((security+2)^2+1)^2+1 := by
    apply (CurrentPublicShiftProgram.encode_work sample.edge.val).trans
    have h := CurrentPublicShiftProgram.edge_size security sample.edge
    gcongr
  have hr := CurrentEmissionRootOrder.positions_work security layout sample.core
  have hij := injection_work security
  have hpe := endpointPermutation_work security sample.core
  change metadata.work + q.work + qbits.work + scales.work + shears.work + intercept.work + shift.work + closure.work +
    roots.work + matrix.work + initial.work + inj.work + perm.work + columns.work + offsetLoad.work + inverse.work + 16 ≤ _
  change qbits.work ≤ _ at hqw
  change q.work ≤ _ at hqs
  change scales.work ≤ fieldWork security at hsc
  change shears.work ≤ fieldWork security at hsh
  change intercept.work ≤ fieldWork security at hiv
  change shift.work ≤ shiftWork security at hsw
  change closure.work ≤ 50*((security+2)^2+1)^2+1 at hcw
  change roots.work ≤ _ at hr
  change matrix.work ≤ _ at hmx
  change initial.work ≤ _ at hinit
  change inj.work ≤ _ at hij
  change perm.work ≤ _ at hpe
  change columns.work ≤ _ at hcwork
  change offsetLoad.work ≤ _ at hp
  change inverse.work ≤ _ at ho'
  unfold assembledWork
  dsimp only [bits,metadata,Size] at *
  norm_num only [Nat.add_assoc] at hcwork ⊢
  omega


def fallbackWork (security : ℕ) : ℕ :=
  let size := Size security
  (current security).work + (size * (size*(6*size+6)+6*size+9)+2) + (3*size+2) + 3

 theorem fallback_work (security : ℕ) :
    (CurrentBinaryAffineEmitter.fallback security).work ≤ fallbackWork security := by
  have hsize : Size security = (current security).edges+1 := rfl
  have hcolumn (column : Fin (Size security)) : (CurrentBinaryAffineEmitter.fallbackColumn security column).work ≤
      Size security*(6*Size security+6)+6*Size security+7 := by
    have hedges := storeData_work (current security).edges (6*Size security+4)
      (fun row : Fin (current security).edges =>
        let tested := equalCounter row.val column.val
        (⟨if tested.value then IntegerBits.one else IntegerBits.zero, tested.work+2⟩ : CountedValue IntegerBits)) (by
          intro row
          have h := equalCounter_work row.val column.val
          have hr := row.isLt
          have hc := column.isLt
          change (equalCounter row.val column.val).work+2 ≤ _
          omega)
    have hhit := equalCounter_work column.val (current security).edges
    have hcol := column.isLt
    have hm : (current security).edges*(6*Size security+4+2) ≤ Size security*(6*Size security+6) := by
      norm_num only [Nat.add_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    change (storeData _ _).work + (equalCounter _ _).work + 3 ≤ _
    omega
  have hcolumns := storeData_work (Size security) _ _ hcolumn
  have hoffset := storeData_work (current security).edges 1 (fun _ => (⟨IntegerBits.zero,1⟩ : CountedValue IntegerBits)) (fun _ => le_rfl)
  have ho : (current security).edges*(1+2) ≤ 3*Size security := by omega
  change (current security).work + (storeData _ _).work + (storeData _ _).work + 3 ≤ _
  unfold fallbackWork
  norm_num only [Nat.add_assoc] at hcolumns ⊢
  omega


noncomputable def guardWork (security : ℕ) : ℕ := BinaryCoreCharge.workPolynomial.eval security +
  Parameters.legCount security*(3*Parameters.legCount security+3*Parameters.modulus security+11)+3


noncomputable def workBound (security : ℕ) : ℕ := assembledWork security + fallbackWork security + guardWork security + 2

 theorem emit_work (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (input : Option (CurrentMaterializedCompletion.Result security)) :
    (CurrentBinaryAffineEmitter.emit security layout input).work ≤ workBound security := by
  cases input with
  | none => exact (fallback_work security).trans (by unfold workBound; omega)
  | some sample =>
    have ha := assembled_work security layout sample
    have hf := fallback_work security
    have hg := CurrentBinaryAffineGuard.current_work security sample.core sample.charts
    have hc := BinaryCoreCharge.polynomial_work security sample.core
    have hguard : (CurrentBinaryAffineGuard.current security sample.core sample.charts).work ≤ guardWork security := by
      unfold guardWork
      omega
    unfold CurrentBinaryAffineEmitter.emit
    dsimp only
    split_ifs <;> change _ + _ + 2 ≤ _ <;> unfold workBound <;> omega

end CurrentAFT.CurrentBinaryEmitterResources

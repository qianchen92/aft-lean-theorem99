import CurrentAFT.BinaryRectangleAddress
import CurrentAFT.CurrentBinaryRectangleDecode

/-! Actual flat-address decoding and zero padding around a finite response entry. -/
namespace CurrentAFT.BinaryRectangleEntry
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryRectangleMaterialization CurrentBinaryRectangleDecode
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def decodeFlat (security order : ℕ) (index : Fin (Size security order)) : CountedValue (Option (Data security order)) :=
  let address := BinaryRectangleAddress.current security order index
  let decoded := CurrentBinaryRectangleDecode.current security order address.value.1 address.value.2
  ⟨decoded.value,address.work+decoded.work+2⟩

def current (security order : ℕ) (entry : Data security order → Data security order → CountedValue RationalBits)
    (output input : Fin (Size security order)) : CountedValue RationalBits :=
  let out := decodeFlat security order output
  let source := decodeFlat security order input
  match out.value,source.value with
  | some outData,some sourceData =>
    let result := entry outData sourceData
    ⟨result.value,out.work+source.work+result.work+4⟩
  | _,_ => ⟨zero,out.work+source.work+3⟩

theorem decodeFlat_value (security order : ℕ) (index : Fin (Size security order)) :
    (decodeFlat security order index).value.map (semanticPoint security order)=
      CurrentRectangleIndex.decode security order (finProdFinEquiv.symm index) := by
  unfold decodeFlat
  rw [CurrentBinaryRectangleDecode.current_value,BinaryRectangleAddress.current_value]

theorem current_value (security order : ℕ) (entry : Data security order → Data security order → CountedValue RationalBits)
    (matrix : CurrentRectangleIndex.Point security order → CurrentRectangleIndex.Point security order → ℚ)
    (he : ∀ output input, (entry output input).value.decode=matrix (semanticPoint security order output) (semanticPoint security order input))
    (output input : Fin (Size security order)) :
    (current security order entry output input).value.decode=
      CurrentRectangleIndex.defect security order matrix (finProdFinEquiv.symm output) (finProdFinEquiv.symm input) := by
  unfold CurrentRectangleIndex.defect CalibrationRectanglePadding.defect
  rw [← decodeFlat_value security order output,← decodeFlat_value security order input]
  unfold current
  cases ho : (decodeFlat security order output).value <;> cases hi : (decodeFlat security order input).value <;>
    simp only [ho,hi,Option.map_none,Option.map_some,Option.elim_none,Option.elim_some,zero_value,he]

noncomputable section
noncomputable def decodeWorkPolynomial (order : ℕ) : Polynomial ℕ :=
  BinaryRectangleAddress.workPolynomial order+CurrentBinaryRectangleDecode.workPolynomial order+2
noncomputable def workPolynomial (order : ℕ) (entryWork : Polynomial ℕ) : Polynomial ℕ :=
  2*decodeWorkPolynomial order+entryWork+4

theorem decodeFlat_work (security order : ℕ) (index : Fin (Size security order)) :
    (decodeFlat security order index).work≤(decodeWorkPolynomial order).eval security := by
  have ha := BinaryRectangleAddress.current_work security order index
  have hd := CurrentBinaryRectangleDecode.current_work security order
    (BinaryRectangleAddress.current security order index).value.1 (BinaryRectangleAddress.current security order index).value.2
  change _+_+2 ≤ _
  simp only [decodeWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  omega

attribute [local irreducible] decodeFlat

theorem current_bounds (security order : ℕ) (entry : Data security order → Data security order → CountedValue RationalBits)
    (entryHeight entryWork : Polynomial ℕ)
    (he : ∀ output input, HeightBound (entry output input).value.decode (entryHeight.eval security) ∧
      (entry output input).work≤entryWork.eval security)
    (output input : Fin (Size security order)) :
    HeightBound (current security order entry output input).value.decode (entryHeight.eval security) ∧
      (current security order entry output input).work≤(workPolynomial order entryWork).eval security := by
  have ho := decodeFlat_work security order output
  have hi := decodeFlat_work security order input
  unfold current
  dsimp only
  cases hout : (decodeFlat security order output).value with
  | none =>
    cases hin : (decodeFlat security order input).value <;> dsimp only
    all_goals refine ⟨HeightBound.zero.mono (Nat.zero_le _),?_⟩
    all_goals simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    all_goals omega
  | some out =>
    cases hin : (decodeFlat security order input).value with
    | none =>
      dsimp only
      refine ⟨HeightBound.zero.mono (Nat.zero_le _),?_⟩
      simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
      omega
    | some source =>
      dsimp only
      have h := he out source
      refine ⟨h.1,?_⟩
      simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
      omega

end
end CurrentAFT.BinaryRectangleEntry

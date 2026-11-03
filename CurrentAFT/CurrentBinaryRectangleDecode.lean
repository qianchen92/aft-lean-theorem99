import CurrentAFT.BinaryRectangleDecodeResources
import CurrentAFT.BinaryRectangleDecodeSemantic
import CurrentAFT.CurrentReferenceCacheWork

/-! Actual current-parameter rectangular decoding. The checked prime and safe
margin are computed by the proposal counters; returned arrays are precisely
the native palette words used by the coefficient programs. -/
namespace CurrentAFT.CurrentBinaryRectangleDecode
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram GradedControlAlgebra
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus

abbrev Data (security order : ℕ) :=
  BinaryRectangleDecode.Data (CurrentReferenceDraw.counts security).colors order (CurrentReferenceDraw.counts security).margin

 theorem colors_eq (security : ℕ) : (CurrentReferenceDraw.counts security).colors=CurrentRectangleIndex.colors security := rfl

 theorem colors_positive (security : ℕ) : 0<(CurrentReferenceDraw.counts security).colors :=
  CurrentReferenceDraw.colors_positive security

 theorem margin_eq (security : ℕ) : (CurrentReferenceDraw.counts security).margin=3*(security+2)^2 :=
  BinaryBodyProgram.margin_value security

 theorem safe_iff (security : ℕ) (color : Fin (CurrentRectangleIndex.colors security)) :
    (CurrentReferenceDraw.counts security).margin≤color.val ∧
        color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors ↔
      CurrentRectangleIndex.safe security color := by
  rw [margin_eq,colors_eq]
  unfold CurrentRectangleIndex.safe
  omega


def safeEquiv (security : ℕ) :
    {color : Fin (CurrentReferenceDraw.counts security).colors //
      (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors} ≃
    {color : Fin (CurrentRectangleIndex.colors security) // CurrentRectangleIndex.safe security color} where
  toFun color := ⟨color.val,(safe_iff security color.val).mp color.property⟩
  invFun color := ⟨color.val,(safe_iff security color.val).mpr color.property⟩
  left_inv _ := rfl
  right_inv _ := rfl


def nativePointEquiv (security order : ℕ) :
    RectanglePointIndex.Point (CurrentReferenceDraw.counts security).colors order
      (fun color => (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors) ≃
    RectanglePointIndex.Point (CurrentRectangleIndex.colors security) order (CurrentRectangleIndex.safe security) :=
  Equiv.sigmaCongrRight (fun arity : TruncatedArity order =>
    Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight (fun _ : Fin arity.val.2.val => safeEquiv security)))


def pointEquiv (security order : ℕ) :
    RectanglePointIndex.Point (CurrentReferenceDraw.counts security).colors order
      (fun color => (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors) ≃
    CurrentRectangleIndex.Point security order :=
  (nativePointEquiv security order).trans (CurrentRectangleIndex.pointEquiv security order)


def semanticPoint (security order : ℕ) (data : Data security order) : CurrentRectangleIndex.Point security order :=
  pointEquiv security order data.point


 theorem semanticPoint_arity (security order : ℕ) (data : Data security order) :
    (semanticPoint security order data).1=data.arity := rfl

 theorem semanticPoint_primary_value (security order : ℕ) (data : Data security order) (index : Fin data.arity.val.1.val) :
    ((semanticPoint security order data).2.1 index).val=(data.primary.get index).val := rfl

 theorem semanticPoint_body_value (security order : ℕ) (data : Data security order) (index : Fin data.arity.val.2.val) :
    ((semanticPoint security order data).2.2 index).val.val=(data.body.get index).val := rfl


def current (security order : ℕ) (row : Fin ((order+1)^2)) (column : Fin ((CurrentReferenceDraw.counts security).colors^order)) :
    CountedValue (Option (Data security order)) :=
  let counts := CurrentReferenceDraw.counts security
  let result := BinaryRectangleDecode.current counts.colors order counts.margin (colors_positive security) row column
  ⟨result.value,counts.work+result.work+1⟩

 theorem encode_pointEquiv (security order : ℕ)
    (point : RectanglePointIndex.Point (CurrentReferenceDraw.counts security).colors order
      (fun color => (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors)) :
    CurrentRectangleIndex.encode security order (pointEquiv security order point)=
      RectanglePointIndex.encode (CurrentReferenceDraw.counts security).colors order (colors_positive security) _ point := by
  change RectanglePointIndex.encode (CurrentRectangleIndex.colors security) order _ _
      ((CurrentRectangleIndex.pointEquiv security order).symm
        ((CurrentRectangleIndex.pointEquiv security order) ((nativePointEquiv security order) point))) = _
  rw [Equiv.symm_apply_apply]
  rfl

 theorem decode_mapped (security order : ℕ) (row : Fin ((order+1)^2))
    (column : Fin ((CurrentReferenceDraw.counts security).colors^order)) :
    (RectanglePointIndex.decode (CurrentReferenceDraw.counts security).colors order (colors_positive security)
      (fun color => (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors)
      (row,column)).map (pointEquiv security order) = CurrentRectangleIndex.decode security order (row,column) := by
  cases hr : RectanglePointIndex.decode (CurrentReferenceDraw.counts security).colors order (colors_positive security)
      (fun color => (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors)
      (row,column) with
  | none =>
    cases ha : CurrentRectangleIndex.decode security order (row,column) with
    | none => rfl
    | some actual =>
      have he := (CurrentRectangleIndex.decode_eq_some security order (row,column) actual).mp ha
      have hraw := (RectanglePointIndex.decode_eq_some (CurrentReferenceDraw.counts security).colors order (colors_positive security)
        (fun color => (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors)
        (row,column) ((pointEquiv security order).symm actual)).mpr (by
          rw [← encode_pointEquiv,Equiv.apply_symm_apply]
          exact he)
      rw [hr] at hraw
      cases hraw
  | some raw =>
    simp only [Option.map_some]
    symm
    apply (CurrentRectangleIndex.decode_eq_some security order (row,column) _).mpr
    rw [encode_pointEquiv]
    exact (RectanglePointIndex.decode_eq_some _ _ _ _ _ _).mp hr

 theorem current_value (security order : ℕ) (row : Fin ((order+1)^2))
    (column : Fin ((CurrentReferenceDraw.counts security).colors^order)) :
    (current security order row column).value.map (semanticPoint security order)=
      CurrentRectangleIndex.decode security order (row,column) := by
  have h := BinaryRectangleDecode.current_value (CurrentReferenceDraw.counts security).colors order
    (CurrentReferenceDraw.counts security).margin (colors_positive security) row column
  have hm := congrArg (fun value => value.map (pointEquiv security order)) h
  dsimp only at hm
  rw [Option.map_map] at hm
  exact hm.trans (decode_mapped security order row column)

noncomputable section


def workPolynomial (order : ℕ) : Polynomial ℕ :=
  CurrentReferenceCacheWork.countsWorkPolynomial+
    BinaryRectangleDecodeResources.workPolynomial order CurrentProposalResources.primeSizePolynomial (3*(Polynomial.X+2)^2)+1

 theorem current_work (security order : ℕ) (row : Fin ((order+1)^2))
    (column : Fin ((CurrentReferenceDraw.counts security).colors^order)) :
    (current security order row column).work ≤ (workPolynomial order).eval security := by
  have hb : (CurrentReferenceDraw.counts security).colors ≤ CurrentProposalResources.primeSizePolynomial.eval security := by
    rw [(CurrentReferenceDraw.counts_values security).1]
    simpa only [CurrentProposalResources.primeSizePolynomial,Parameters.base,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat] using (Parameters.modulus_bounds security).2
  have hm : (CurrentReferenceDraw.counts security).margin ≤ (3*(Polynomial.X+2)^2:Polynomial ℕ).eval security := by
    rw [margin_eq]
    simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
    exact le_rfl
  have h := BinaryRectangleDecodeResources.current_polynomial_work security (CurrentReferenceDraw.counts security).colors order
    (CurrentReferenceDraw.counts security).margin (colors_positive security) row column
    CurrentProposalResources.primeSizePolynomial (3*(Polynomial.X+2)^2) hb hm
  have hc := CurrentReferenceCacheWork.counts_work security
  change (CurrentReferenceDraw.counts security).work+(BinaryRectangleDecode.current _ _ _ _ _ _).work+1 ≤ _
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_one]
  omega

end
end CurrentAFT.CurrentBinaryRectangleDecode

import CurrentAFT.BinaryRectangleResources
import AFT.BinaryCounterDivision

/-! Executed flattening inverse for the actual rectangular calibration arrays. -/
namespace CurrentAFT.BinaryRectangleAddress
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryRectangleMaterialization
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] dimensions

def current (security order : ℕ) (index : Fin (Size security order)) :
    CountedValue (CurrentRectangleIndex.Rectangle security order) :=
  let dims := dimensions security order
  let division := divideCounter index.val dims.columns
  let row : Fin ((order+1)^2) := ⟨division.quotient, by
    have hp : 0<dims.columns := by rw [(dimensions_values security order).2.1]; exact pow_pos (CurrentRectangleIndex.colors_pos security) _
    rw [(divideCounter_value index.val dims.columns hp).1]
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [(dimensions_values security order).2.1]
    exact index.isLt⟩
  let column : Fin ((CurrentRectangleIndex.colors security)^order) := ⟨division.remainder,by
    have hp : 0<dims.columns := by rw [(dimensions_values security order).2.1]; exact pow_pos (CurrentRectangleIndex.colors_pos security) _
    rw [(divideCounter_value index.val dims.columns hp).2,← (dimensions_values security order).2.1]
    exact Nat.mod_lt _ hp⟩
  ⟨(row,column),dims.work+division.work+3⟩

theorem current_value (security order : ℕ) (index : Fin (Size security order)) :
    (current security order index).value=finProdFinEquiv.symm index := by
  have hp : 0<(dimensions security order).columns := by
    rw [(dimensions_values security order).2.1]
    exact pow_pos (CurrentRectangleIndex.colors_pos security) _
  apply Prod.ext <;> apply Fin.ext
  · change (divideCounter index.val (dimensions security order).columns).quotient = _
    rw [(divideCounter_value _ _ hp).1,(dimensions_values security order).2.1]
    rfl
  · change (divideCounter index.val (dimensions security order).columns).remainder = _
    rw [(divideCounter_value _ _ hp).2,(dimensions_values security order).2.1]
    rfl

noncomputable section
noncomputable def workPolynomial (order : ℕ) : Polynomial ℕ :=
  BinaryRectangleResources.dimensionsPolynomial order+
    500*(BinaryRectangleResources.sizePolynomial order+BinaryRectangleResources.columnsPolynomial order+2)^2+3

theorem current_work (security order : ℕ) (index : Fin (Size security order)) :
    (current security order index).work≤(workPolynomial order).eval security := by
  have hp : 0<(dimensions security order).columns := by
    rw [(dimensions_values security order).2.1]
    exact pow_pos (CurrentRectangleIndex.colors_pos security) _
  have hw := divideCounter_work index.val (dimensions security order).columns hp
  have hi : index.val≤(BinaryRectangleResources.sizePolynomial order).eval security :=
    index.isLt.le.trans (BinaryRectangleResources.size_bound security order)
  have hc : (dimensions security order).columns≤(BinaryRectangleResources.columnsPolynomial order).eval security := by
    rw [(dimensions_values security order).2.1]
    exact BinaryRectangleResources.columns_bound security order
  have hw' := hw.trans (show 500*(index.val+(dimensions security order).columns+2)^2 ≤
    500*((BinaryRectangleResources.sizePolynomial order).eval security+(BinaryRectangleResources.columnsPolynomial order).eval security+2)^2 by gcongr)
  have hd := BinaryRectangleResources.dimensions_polynomial_work security order
  change _+_+3≤_
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat]
  omega

end
end CurrentAFT.BinaryRectangleAddress

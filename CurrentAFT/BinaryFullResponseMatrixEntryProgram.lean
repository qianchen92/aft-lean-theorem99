import CurrentAFT.BinaryRectangleEntry
import CurrentAFT.BinaryNaturalCoordinates
import CurrentAFT.BinaryFullResponseResources
import CurrentAFT.RationalFullResponseMatrix

/-! The actual full-response program inserted into each valid rectangular entry.
Every query-buffer copy, address decode, and zero-padding branch is executed. -/
namespace CurrentAFT.BinaryFullResponseMatrixEntry
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFullResponseData BinaryRectangleMaterialization
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def validEntry (security bits order : ℕ) (data : Data order)
    (output source : CurrentBinaryRectangleDecode.Data security order) : CountedValue RationalBits :=
  let primary := BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.primary
  let body := BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.body
  let value := BinaryFullResponseProgram.current security bits order data source.arity source.primary source.body output.arity primary.value body.value
  ⟨value.value,primary.work+body.work+value.work+3⟩

def current (security bits order : ℕ) (data : Data order)
    (output source : Fin (Size security order)) : CountedValue RationalBits :=
  BinaryRectangleEntry.current security order (validEntry security bits order data) output source

noncomputable section
attribute [local irreducible] PublicParameterProgram.modulus
  BinaryFullResponseProgram.current BinaryNaturalCoordinates.current

noncomputable def heightPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFullResponseResources.heightPolynomial order data precision
noncomputable def validWorkPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFullResponseResources.workPolynomial order data precision+Polynomial.C (2*order*(3*order+6)+7)
noncomputable def workPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRectangleEntry.workPolynomial order (validWorkPolynomial order data precision)

theorem validEntry_bounds (security order : ℕ) (data : Data order) (precision : Polynomial ℕ)
    (output source : CurrentBinaryRectangleDecode.Data security order) :
    HeightBound (validEntry security (precision.eval security) order data output source).value.decode
      ((heightPolynomial order data precision).eval security) ∧
      (validEntry security (precision.eval security) order data output source).work≤
        (validWorkPolynomial order data precision).eval security := by
  let primary := BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.primary
  let body := BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.body
  have h := BinaryFullResponseResources.current_bounds security order data precision source.arity source.primary source.body output.arity
    primary.value body.value (BinaryNaturalCoordinates.current_valid _ _) (BinaryNaturalCoordinates.current_valid _ _)
  have wp := BinaryNaturalCoordinates.current_work (CurrentBinaryRectangleDecode.colors_positive security) output.primary
  have wb := BinaryNaturalCoordinates.current_work (CurrentBinaryRectangleDecode.colors_positive security) output.body
  have ha := output.arity.property
  have wpp : primary.work≤order*(3*order+6)+2 := wp.trans (by gcongr <;> omega)
  have wbb : body.work≤order*(3*order+6)+2 := wb.trans (by gcongr <;> omega)
  refine ⟨h.1,?_⟩
  change primary.work+body.work+_+3≤_
  simp only [validWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C,Nat.mul_assoc]
  dsimp only [primary,body] at h wpp wbb ⊢
  omega

theorem current_bounds (security order : ℕ) (data : Data order) (precision : Polynomial ℕ)
    (output source : Fin (Size security order)) :
    HeightBound (current security (precision.eval security) order data output source).value.decode
      ((heightPolynomial order data precision).eval security) ∧
      (current security (precision.eval security) order data output source).work≤
        (workPolynomial order data precision).eval security :=
  BinaryRectangleEntry.current_bounds security order (validEntry security (precision.eval security) order data)
    (heightPolynomial order data precision) (validWorkPolynomial order data precision)
    (validEntry_bounds security order data precision) output source

end
end CurrentAFT.BinaryFullResponseMatrixEntry

import CurrentAFT.BinaryRectangleMaterialization

/-! Polynomial resources for producing the complete rectangular matrix,
its exact scalar right-hand side, and the stored calibration iterate. -/
namespace CurrentAFT.BinaryRectangleResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryArithmetic.RationalBits BinaryRectangleMaterialization
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def dimensionsWork (security order : ℕ) : ℕ :=
  let q := CurrentRectangleIndex.colors security
  PublicParameterProgram.workBound security + (2*order+1) + powerCounterWork (order+1) 2 +
    powerCounterWork q order + ((order+1)^2*(2*q^order+3)+1) + 5

 theorem dimensions_work (security order : ℕ) : (dimensions security order).work ≤ dimensionsWork security order := by
  have hq := PublicParameterProgram.modulus_work security
  have hs := addCounter_work order 1
  have hr := powerCounter_work (addCounter order 1).count 2
  have hc := powerCounter_work (PublicParameterProgram.modulus security).count order
  have hm := multiplyCounter_work (powerCounter (addCounter order 1).count 2).count
    (powerCounter (PublicParameterProgram.modulus security).count order).count
  have hm' : (multiplyCounter (powerCounter (addCounter order 1).count 2).count
      (powerCounter (PublicParameterProgram.modulus security).count order).count).work ≤
      (order+1)^2*(2*(PublicParameterProgram.modulus security).count^order+3)+1 := by
    simpa only [powerCounter_value,addCounter_value] using hm.le
  change (PublicParameterProgram.modulus security).work + (addCounter order 1).work +
    (powerCounter (addCounter order 1).count 2).work + (powerCounter (PublicParameterProgram.modulus security).count order).work +
    (multiplyCounter (powerCounter (addCounter order 1).count 2).count (powerCounter (PublicParameterProgram.modulus security).count order).count).work+5 ≤ _
  have hr' : (powerCounter (addCounter order 1).count 2).work ≤ powerCounterWork (order+1) 2 := by
    simpa only [addCounter_value] using powerCounter_work (addCounter order 1).count 2
  unfold dimensionsWork
  change _ ≤ PublicParameterProgram.workBound security + (2*order+1)+powerCounterWork (order+1) 2+
    powerCounterWork (PublicParameterProgram.modulus security).count order + ((order+1)^2*(2*(PublicParameterProgram.modulus security).count^order+3)+1)+5
  omega


def currentWork (security order entryWork : ℕ) : ℕ :=
  let size := Size security order
  dimensionsWork security order + (size*(size*(entryWork+2)+4)+2) + (size*(3*size+6)+2) + size+3

 theorem current_work (security order entryWork : ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits)
    (hw : ∀ output input, (entry output input).work ≤ entryWork) :
    (current security order entry).work ≤ currentWork security order entryWork := by
  let dims := dimensions security order
  have hd := dimensions_work security order
  have he := (dimensions_values security order).2.2
  have hm := storeData_work dims.size (dims.size*(entryWork+2)+2)
    (fun output => storeData dims.size (fun input => entry (output.cast he) (input.cast he)))
    (fun output => storeData_work dims.size entryWork _ (fun input => hw _ _))
  have hr := storeData_work dims.size (3*dims.size+4) (fun output => rhsEntry output.val) (by
    intro output
    have h := equalCounter_work output.val 0
    have ho := output.isLt
    change (equalCounter output.val 0).work+2 ≤ _
    omega)
  have hm' := hm.trans (show dims.size*(dims.size*(entryWork+2)+2+2)+2 ≤
      (Size security order)*((Size security order)*(entryWork+2)+4)+2 by rw [he])
  have hr' := hr.trans (show dims.size*(3*dims.size+4+2)+2 ≤
      (Size security order)*(3*(Size security order)+6)+2 by rw [he])
  change dims.work + (storeData _ _).work + (storeData _ _).work + dims.size+3 ≤ _
  change dims.size = Size security order at he
  change dims.work ≤ _ at hd
  unfold currentWork
  norm_num only [Nat.add_assoc] at hm hr ⊢
  dsimp only [dims] at *
  have hsize := (dimensions_values security order).2.2
  omega

noncomputable section
open scoped BigOperators


def columnsPolynomial (order : ℕ) : Polynomial ℕ := CurrentProposalResources.primeSizePolynomial^order

def sizePolynomial (order : ℕ) : Polynomial ℕ := Polynomial.C ((order+1)^2)*columnsPolynomial order

 theorem colors_bound (security : ℕ) : CurrentRectangleIndex.colors security ≤ CurrentProposalResources.primeSizePolynomial.eval security := by
  rw [CurrentRectangleIndex.colors_eq]
  simpa only [CurrentProposalResources.primeSizePolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat, Parameters.base] using (Parameters.modulus_bounds security).2

 theorem columns_bound (security order : ℕ) : (CurrentRectangleIndex.colors security)^order ≤ (columnsPolynomial order).eval security := by
  simp only [columnsPolynomial, Polynomial.eval_pow]
  exact Nat.pow_le_pow_left (colors_bound security) order

 theorem size_bound (security order : ℕ) : Size security order ≤ (sizePolynomial order).eval security := by
  simp only [Size,sizePolynomial,Polynomial.eval_mul,Polynomial.eval_C]
  exact Nat.mul_le_mul_left _ (columns_bound security order)


def dimensionsPolynomial (order : ℕ) : Polynomial ℕ :=
  let q := CurrentProposalResources.primeSizePolynomial
  PublicParameterProgram.workPolynomial + Polynomial.C (2*order+1+powerCounterWork (order+1) 2) +
    Polynomial.C (order+1)*(6*(q+1)^(order+2)+4) + Polynomial.C ((order+1)^2)*(2*q^order+3)+6

 theorem dimensions_polynomial_work (security order : ℕ) :
    (dimensions security order).work ≤ (dimensionsPolynomial order).eval security := by
  apply (dimensions_work security order).trans
  have hq := colors_bound security
  have hp := Nat.pow_le_pow_left hq order
  have hc := powerCounterWork_mono hq order
  simp only [dimensionsWork,dimensionsPolynomial,powerCounterWork,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one,
    PublicParameterProgram.workPolynomial_eval] at *
  have hm := Nat.mul_le_mul_left ((order+1)^2) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 3)
  omega


def currentPolynomial (order : ℕ) (entryWork : Polynomial ℕ) : Polynomial ℕ :=
  let size := sizePolynomial order
  dimensionsPolynomial order + (size*(size*(entryWork+2)+4)+2) + (size*(3*size+6)+2)+size+3

 theorem current_polynomial_work (security order : ℕ) (entryWork : Polynomial ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits)
    (hw : ∀ output input, (entry output input).work ≤ entryWork.eval security) :
    (current security order entry).work ≤ (currentPolynomial order entryWork).eval security := by
  apply (current_work security order (entryWork.eval security) entry hw).trans
  have hs := size_bound security order
  have hd : dimensionsWork security order ≤ (dimensionsPolynomial order).eval security := by
    have hq := colors_bound security
    have hc := powerCounterWork_mono hq order
    have hp := Nat.pow_le_pow_left hq order
    have hm := Nat.mul_le_mul_left ((order+1)^2) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 3)
    simp only [dimensionsWork, dimensionsPolynomial,powerCounterWork,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one,
      PublicParameterProgram.workPolynomial_eval] at *
    omega
  simp only [currentWork,currentPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr


def runPolynomial (order : ℕ) (entryHeight entryWork steps : Polynomial ℕ) : Polynomial ℕ :=
  currentPolynomial order entryWork +
    BinaryRectangleIteration.workPolynomial (Polynomial.C ((order+1)^2)) (columnsPolynomial order) entryHeight steps + 1

 theorem run_polynomial_bounds (security order steps : ℕ) (entryHeight entryWork stepsBound : Polynomial ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits)
    (hh : ∀ output input, HeightBound (entry output input).value.decode (entryHeight.eval security))
    (hw : ∀ output input, (entry output input).work ≤ entryWork.eval security)
    (hs : steps ≤ stepsBound.eval security) :
    (run security order steps entry).work ≤ (runPolynomial order entryHeight entryWork stepsBound).eval security ∧
      ∀ row column, HeightBound (((run security order steps entry).value.get row).get column).decode
        ((BinaryCalibrationIteration.heightPolynomial (sizePolynomial order) entryHeight stepsBound).eval security) := by
  have hm : ∀ output input, HeightBound (((current security order entry).matrix.get output).get input).decode (entryHeight.eval security) := by
    intro output input
    rw [matrix_value]
    exact hh output input
  have hr : ∀ output, HeightBound ((current security order entry).rhs.get output).decode (entryHeight.eval security) := by
    intro output
    rw [rhs_value]
    split_ifs
    · exact HeightBound.one.mono (Nat.zero_le _)
    · exact HeightBound.zero.mono (Nat.zero_le _)
  have hp := BinaryRectangleIteration.polynomial_work security ((order+1)^2) ((CurrentRectangleIndex.colors security)^order) steps
    (Polynomial.C ((order+1)^2)) (columnsPolynomial order) entryHeight stepsBound (current security order entry).matrix (current security order entry).rhs
    (by simp only [Polynomial.eval_C,le_refl]) (columns_bound security order) hs hm hr
  have ht := BinaryRectangleIteration.polynomial_height security ((order+1)^2) ((CurrentRectangleIndex.colors security)^order) steps
    (Polynomial.C ((order+1)^2)) (columnsPolynomial order) entryHeight stepsBound (current security order entry).matrix (current security order entry).rhs
    (by simp only [Polynomial.eval_C,le_refl]) (columns_bound security order) hs hm hr
  have hc := current_polynomial_work security order entryWork entry hw
  constructor
  · change (current security order entry).work + (BinaryRectangleIteration.run _ _ _ _ _).work+1 ≤ _
    simp only [runPolynomial,Polynomial.eval_add,Polynomial.eval_one]
    omega
  · intro row column
    exact ht row column

end
end CurrentAFT.BinaryRectangleResources

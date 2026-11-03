import CurrentAFT.BinaryCalibrationIteration
import CurrentAFT.CurrentRectangleIndex
import AFT.BinaryDataArrays
import AFT.UnaryPolynomialCounters

/-! # Materialized calibration output in the joint weight array layout

Both counter arithmetic for flattening and sequential array copying are
executed. The shared matrix iteration keeps its common-denominator height
bound, and every retained coordinate has the exact original rational value.
-/
namespace CurrentAFT.BinaryRectangleIteration
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] multiplyCounter addCounter

def position (rows columns : ℕ) (row : Fin rows) (column : Fin columns) : UnaryCounterResult :=
  let multiplied := multiplyCounter columns row.val
  let added := addCounter multiplied.count column.val
  ⟨added.count, multiplied.work + added.work + 2⟩

theorem position_value (rows columns : ℕ) (row : Fin rows) (column : Fin columns) :
    (position rows columns row column).count = (finProdFinEquiv (row, column)).val := by
  simp only [position, addCounter_value, multiplyCounter_value]
  change columns * row.val + column.val = column.val + columns * row.val
  omega

def entry (rows columns : ℕ) (vector : Vector RationalBits (rows*columns))
    (row : Fin rows) (column : Fin columns) : CountedValue RationalBits :=
  let index := position rows columns row column
  let stored := readVector zero vector ⟨index.count, by rw [position_value]; exact (finProdFinEquiv (row, column)).isLt⟩
  ⟨stored.value, index.work + stored.work + 1⟩

def reshape (rows columns : ℕ) (vector : Vector RationalBits (rows*columns)) :
    CountedValue (Vector (Vector RationalBits columns) rows) :=
  storeData rows (fun row => storeData columns (entry rows columns vector row))

theorem entry_value (rows columns : ℕ) (vector : Vector RationalBits (rows*columns))
    (row : Fin rows) (column : Fin columns) :
    (entry rows columns vector row column).value = vector.get (finProdFinEquiv (row, column)) := by
  simp only [entry, readVector_value]
  congr 1
  exact Fin.ext (position_value rows columns row column)

theorem reshape_get (rows columns : ℕ) (vector : Vector RationalBits (rows*columns))
    (row : Fin rows) (column : Fin columns) :
    ((reshape rows columns vector).value.get row).get column = vector.get (finProdFinEquiv (row, column)) := by
  simp only [reshape, storeData_get, entry_value]

def entryWork (rows columns : ℕ) : ℕ :=
  columns*(2*rows+3)+2*(columns*rows)+3*(rows*columns)+8

def reshapeWork (rows columns : ℕ) : ℕ := rows*(columns*(entryWork rows columns+2)+4)+2

theorem entry_work (rows columns : ℕ) (vector : Vector RationalBits (rows*columns))
    (row : Fin rows) (column : Fin columns) :
    (entry rows columns vector row column).work ≤ entryWork rows columns := by
  have hm := multiplyCounter_work columns row.val
  have ha : (addCounter (multiplyCounter columns row.val).count column.val).work ≤
      2 * (columns * row.val) + 1 :=
    (addCounter_work (multiplyCounter columns row.val).count column.val).le.trans_eq (by rw [multiplyCounter_value])
  have hr := readVector_work zero vector
    (⟨(position rows columns row column).count, by rw [position_value]; exact (finProdFinEquiv (row,column)).isLt⟩ : Fin (rows*columns))
  have hw : row.val ≤ rows := row.isLt.le
  have h1 : columns * (2 * row.val + 3) ≤ columns * (2 * rows + 3) := by gcongr
  have h2 : 2 * (columns * row.val) ≤ 2 * (columns * rows) := by gcongr
  simp only [entry, position, entryWork] at *
  omega

theorem reshape_work (rows columns : ℕ) (vector : Vector RationalBits (rows*columns)) :
    (reshape rows columns vector).work ≤ reshapeWork rows columns :=
  storeData_work rows (columns*(entryWork rows columns+2)+2) _ (fun row =>
    storeData_work columns (entryWork rows columns) _ (entry_work rows columns vector row))

def run (rows columns : ℕ) (matrix : Vector (Vector RationalBits (rows*columns)) (rows*columns))
    (rhs : Vector RationalBits (rows*columns)) (steps : ℕ) :
    CountedValue (Vector (Vector RationalBits columns) rows) :=
  let iterated := iteration matrix rhs steps
  let result := reshape rows columns iterated.data
  ⟨result.value, iterated.work + result.work + 1⟩

theorem run_value (rows columns : ℕ) (matrix : Vector (Vector RationalBits (rows*columns)) (rows*columns))
    (rhs : Vector RationalBits (rows*columns)) (steps : ℕ) (row : Fin rows) (column : Fin columns) :
    (((run rows columns matrix rhs steps).value.get row).get column).decode =
      linearIteration (fun output input => ((matrix.get output).get input).decode)
        (fun output => (rhs.get output).decode) steps (finProdFinEquiv (row, column)) := by
  simp only [run, reshape_get, iteration_value]

theorem run_work (rows columns : ℕ) (matrix : Vector (Vector RationalBits (rows*columns)) (rows*columns))
    (rhs : Vector RationalBits (rows*columns)) (steps bits : ℕ)
    (hmatrix : ∀ output input, HeightBound ((matrix.get output).get input).decode bits)
    (hrhs : ∀ output, HeightBound (rhs.get output).decode bits) :
    (run rows columns matrix rhs steps).work ≤
      steps * iterationWorkStep (rows*columns) bits steps + 2*(rows*columns) + reshapeWork rows columns + 3 := by
  have hi := iteration_work matrix rhs bits steps steps hmatrix hrhs le_rfl
  have hr := reshape_work rows columns (iteration matrix rhs steps).data
  change (iteration matrix rhs steps).work + (reshape rows columns (iteration matrix rhs steps).data).work + 1 ≤ _
  omega

noncomputable def reshapePolynomial (rows columns : Polynomial ℕ) : Polynomial ℕ :=
  rows*(columns*(columns*(2*rows+3)+2*(columns*rows)+3*(rows*columns)+10)+4)+2

theorem reshapePolynomial_eval (rows columns : Polynomial ℕ) (security : ℕ) :
    (reshapePolynomial rows columns).eval security = reshapeWork (rows.eval security) (columns.eval security) := by
  simp [reshapePolynomial, reshapeWork, entryWork]

noncomputable def workPolynomial (rows columns bits steps : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCalibrationIteration.workPolynomial (rows*columns) bits steps + reshapePolynomial rows columns + 1

theorem polynomial_work (security rows columns steps : ℕ)
    (rowsBound columnsBound bitsBound stepsBound : Polynomial ℕ)
    (matrix : Vector (Vector RationalBits (rows*columns)) (rows*columns)) (rhs : Vector RationalBits (rows*columns))
    (hrows : rows ≤ rowsBound.eval security) (hcolumns : columns ≤ columnsBound.eval security)
    (hsteps : steps ≤ stepsBound.eval security)
    (hmatrix : ∀ output input, HeightBound ((matrix.get output).get input).decode (bitsBound.eval security))
    (hrhs : ∀ output, HeightBound (rhs.get output).decode (bitsBound.eval security)) :
    (run rows columns matrix rhs steps).work ≤
      (workPolynomial rowsBound columnsBound bitsBound stepsBound).eval security := by
  have hi := BinaryCalibrationIteration.polynomial_work security (rows*columns) steps
    (rowsBound*columnsBound) bitsBound stepsBound matrix rhs
    (by simpa only [Polynomial.eval_mul] using Nat.mul_le_mul hrows hcolumns) hsteps hmatrix hrhs
  have hr := reshape_work rows columns (iteration matrix rhs steps).data
  have hb : reshapeWork rows columns ≤ (reshapePolynomial rowsBound columnsBound).eval security := by
    rw [reshapePolynomial_eval]
    unfold reshapeWork entryWork
    gcongr
  simp only [run, workPolynomial, Polynomial.eval_add, Polynomial.eval_one]
  omega

theorem polynomial_height (security rows columns steps : ℕ)
    (rowsBound columnsBound bitsBound stepsBound : Polynomial ℕ)
    (matrix : Vector (Vector RationalBits (rows*columns)) (rows*columns)) (rhs : Vector RationalBits (rows*columns))
    (hrows : rows ≤ rowsBound.eval security) (hcolumns : columns ≤ columnsBound.eval security)
    (hsteps : steps ≤ stepsBound.eval security)
    (hmatrix : ∀ output input, HeightBound ((matrix.get output).get input).decode (bitsBound.eval security))
    (hrhs : ∀ output, HeightBound (rhs.get output).decode (bitsBound.eval security))
    (row : Fin rows) (column : Fin columns) :
    HeightBound (((run rows columns matrix rhs steps).value.get row).get column).decode
      ((BinaryCalibrationIteration.heightPolynomial (rowsBound*columnsBound) bitsBound stepsBound).eval security) := by
  simp only [run, reshape_get]
  exact BinaryCalibrationIteration.polynomial_height security (rows*columns) steps
    (rowsBound*columnsBound) bitsBound stepsBound matrix rhs
    (by simpa only [Polynomial.eval_mul] using Nat.mul_le_mul hrows hcolumns) hsteps hmatrix hrhs _

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] CurrentRectangleIndex.colors Parameters.base

variable {Source Target : Type*} [Fintype Source] [Fintype Target]

theorem linearIteration_reindex (equiv : Source ≃ Target) (matrix : Source → Source → ℚ)
    (rhs : Source → ℚ) (steps : ℕ) (point : Source) :
    linearIteration (fun output input => matrix (equiv.symm output) (equiv.symm input))
      (fun output => rhs (equiv.symm output)) steps (equiv point) = linearIteration matrix rhs steps point := by
  induction steps generalizing point with
  | zero => rfl
  | succ steps ih =>
    simp only [linearIteration, Pi.sub_apply, Equiv.symm_apply_apply, RationalNumerics.matrixApply]
    congr 1
    rw [← equiv.sum_comp]
    simp only [Equiv.symm_apply_apply, ih]

theorem actual_value (security order steps : ℕ)
    (rationalMatrix : CurrentRectangleIndex.Point security order → CurrentRectangleIndex.Point security order → ℚ)
    (matrix : Vector (Vector RationalBits (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
      (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
    (rhs : Vector RationalBits (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
    (hmatrix : ∀ output input, ((matrix.get output).get input).decode =
      CurrentRectangleIndex.defect security order rationalMatrix (finProdFinEquiv.symm output) (finProdFinEquiv.symm input))
    (hrhs : ∀ output, (rhs.get output).decode = CurrentRectangleIndex.rhs security order (finProdFinEquiv.symm output))
    (point : CurrentRectangleIndex.Point security order) :
    (((run ((order+1)^2) ((CurrentRectangleIndex.colors security)^order) matrix rhs steps).value.get
      (CurrentRectangleIndex.encode security order point).1).get
      (CurrentRectangleIndex.encode security order point).2).decode =
      linearIteration rationalMatrix (CalibrationMatrixApproximation.rhs security order) steps point := by
  rw [run_value]
  have hm : (fun output input => ((matrix.get output).get input).decode) =
      (fun output input => CurrentRectangleIndex.defect security order rationalMatrix
        (finProdFinEquiv.symm output) (finProdFinEquiv.symm input)) := funext (fun out => funext (hmatrix out))
  have hr : (fun output => (rhs.get output).decode) =
      (fun output => CurrentRectangleIndex.rhs security order (finProdFinEquiv.symm output)) := funext hrhs
  rw [hm, hr]
  have hi := linearIteration_reindex
    (finProdFinEquiv : CurrentRectangleIndex.Rectangle security order ≃
      Fin (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
    (CurrentRectangleIndex.defect security order rationalMatrix) (CurrentRectangleIndex.rhs security order)
    steps (CurrentRectangleIndex.encode security order point)
  exact hi.trans (CurrentRectangleIndex.iteration_at security order rationalMatrix steps point)

end
end CurrentAFT.BinaryRectangleIteration

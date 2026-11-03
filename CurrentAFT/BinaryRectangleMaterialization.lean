import CurrentAFT.BinaryRectangleIteration
import CurrentAFT.BinaryWeightLocal
import CurrentAFT.CurrentProposalResources

/-! Actual counters and full rectangular matrix/rhs buffers before calibration
iteration. The caller supplies the executed numerical entry program; all table
visits and copies, including zero-padded rows, are performed here. -/
namespace CurrentAFT.BinaryRectangleMaterialization
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryArithmetic.RationalBits GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus

abbrev Size (security order : ℕ) := ((order+1)^2)*(CurrentRectangleIndex.colors security)^order

structure Dimensions where
  rows : ℕ
  columns : ℕ
  size : ℕ
  work : ℕ


def dimensions (security order : ℕ) : Dimensions :=
  let modulus := PublicParameterProgram.modulus security
  let successor := addCounter order 1
  let rows := powerCounter successor.count 2
  let columns := powerCounter modulus.count order
  let size := multiplyCounter rows.count columns.count
  ⟨rows.count,columns.count,size.count,modulus.work+successor.work+rows.work+columns.work+size.work+5⟩

 theorem dimensions_values (security order : ℕ) :
    (dimensions security order).rows = (order+1)^2 ∧
    (dimensions security order).columns = (CurrentRectangleIndex.colors security)^order ∧
    (dimensions security order).size = Size security order := by
  simp only [dimensions, powerCounter_value, addCounter_value, multiplyCounter_value,
    CurrentRectangleIndex.colors, Size, and_self]


def rhsEntry (index : ℕ) : CountedValue RationalBits :=
  let hit := equalCounter index 0
  ⟨if hit.value then one else zero, hit.work+2⟩

 theorem rhsEntry_value (index : ℕ) : (rhsEntry index).value.decode = if index = 0 then 1 else 0 := by
  by_cases h : index = 0
  · simp only [rhsEntry, if_pos ((equalCounter_value _ _).mpr h), one_value, if_pos h]
  · simp only [rhsEntry, if_neg (fun hh => h ((equalCounter_value _ _).mp hh)), zero_value, if_neg h]

structure Result (security order : ℕ) where
  matrix : Vector (Vector RationalBits (Size security order)) (Size security order)
  rhs : Vector RationalBits (Size security order)
  work : ℕ


def current (security order : ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits) : Result security order :=
  let dims := dimensions security order
  let matrix := storeData dims.size (fun output => storeData dims.size (fun input =>
    entry (output.cast (dimensions_values security order).2.2) (input.cast (dimensions_values security order).2.2)))
  let rhs := storeData dims.size (fun output => rhsEntry output.val)
  ⟨(matrix.value.map (fun row => row.cast (dimensions_values security order).2.2)).cast (dimensions_values security order).2.2,
    rhs.value.cast (dimensions_values security order).2.2,
    dims.work+matrix.work+rhs.work+dims.size+3⟩

 theorem matrix_value (security order : ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits)
    (output input : Fin (Size security order)) :
    (((current security order entry).matrix.get output).get input) = (entry output input).value := by
  simp only [current, Vector.get_cast, Vector.get_map, storeData_get]
  congr 1

 theorem rhs_value (security order : ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits)
    (output : Fin (Size security order)) :
    ((current security order entry).rhs.get output).decode = if output.val = 0 then 1 else 0 := by
  simp only [current, Vector.get_cast, storeData_get, rhsEntry_value, Fin.val_cast]


def run (security order steps : ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits) :
    CountedValue (BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :=
  let table := current security order entry
  let result := BinaryRectangleIteration.run ((order+1)^2) ((CurrentRectangleIndex.colors security)^order) table.matrix table.rhs steps
  ⟨result.value,table.work+result.work+1⟩

noncomputable section
open scoped Classical
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base


def scalarPoint (security order : ℕ) : CurrentRectangleIndex.Point security order :=
  ⟨zeroArity order,(Fin.elim0,Fin.elim0)⟩

 theorem scalar_point (security order : ℕ) (point : CurrentRectangleIndex.Point security order) :
    point.1 = zeroArity order ↔ point = scalarPoint security order := by
  constructor
  · rintro h
    rcases point with ⟨arity,primary,body⟩
    dsimp only at h
    subst arity
    have hp : primary = (Fin.elim0 : Fin 0 → ActualControls.Palette security) := by funext index; exact Fin.elim0 index
    have hb : body = (Fin.elim0 : Fin 0 → ActualControls.SafePalette security) := by funext index; exact Fin.elim0 index
    subst primary
    subst body
    rfl
  · intro h
    rw [h]
    rfl

 theorem rhs_formula (security order : ℕ) (index : CurrentRectangleIndex.Rectangle security order) :
    CurrentRectangleIndex.rhs security order index =
      if index = CurrentRectangleIndex.encode security order (scalarPoint security order) then 1 else 0 := by
  rw [CurrentRectangleIndex.rhs_eq]
  unfold CalibrationRectanglePadding.extend
  cases hd : CurrentRectangleIndex.decode security order index with
  | none =>
    have hn : index ≠ CurrentRectangleIndex.encode security order (scalarPoint security order) := by
      intro h
      have hs := (CurrentRectangleIndex.decode_eq_some security order index (scalarPoint security order)).mpr h
      rw [hd] at hs
      contradiction
    simp only [Option.elim_none, if_neg hn]
  | some point =>
    simp only [Option.elim_some, CalibrationMatrixApproximation.rhs]
    have he := (CurrentRectangleIndex.decode_eq_some security order index point).mp hd
    have hz : point.1 = zeroArity order ↔ index = CurrentRectangleIndex.encode security order (scalarPoint security order) := by
      rw [scalar_point, he]
      exact (CurrentRectangleIndex.encode security order).injective.eq_iff.symm
    simp only [hz]

 theorem rhs_flat (security order : ℕ) (index : Fin (Size security order)) :
    CurrentRectangleIndex.rhs security order (finProdFinEquiv.symm index) = if index.val = 0 then 1 else 0 := by
  rw [rhs_formula]
  have he : finProdFinEquiv.symm index = CurrentRectangleIndex.encode security order (scalarPoint security order) ↔ index.val = 0 := by
    rw [Equiv.symm_apply_eq, Fin.ext_iff]
    have hp : (CurrentRectangleIndex.pointEquiv security order).symm (scalarPoint security order) =
        (⟨zeroArity order,(Fin.elim0,Fin.elim0)⟩ : RectanglePointIndex.Point (CurrentRectangleIndex.colors security) order (CurrentRectangleIndex.safe security)) := by
      apply (CurrentRectangleIndex.pointEquiv security order).injective
      rw [Equiv.apply_symm_apply]
      simp only [scalarPoint, CurrentRectangleIndex.pointEquiv, Equiv.sigmaCongrRight_apply]
      congr 1
      apply Prod.ext <;> funext index <;> exact Fin.elim0 index
    have hz : (finProdFinEquiv (CurrentRectangleIndex.encode security order (scalarPoint security order))).val = 0 := by
      unfold CurrentRectangleIndex.encode
      dsimp only [Function.Embedding.coeFn_mk]
      rw [hp]
      simp [RectanglePointIndex.encode, WeightCoordinates.arityIndex, WeightCoordinates.arityCode,
        WeightCoordinates.wordIndex, WeightCoordinates.jointCode, WeightCoordinates.tupleCode, zeroArity]
    rw [hz]
  simp only [he]

 theorem run_value (security order steps : ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits)
    (rationalMatrix : CurrentRectangleIndex.Point security order → CurrentRectangleIndex.Point security order → ℚ)
    (hentry : ∀ output input, (entry output input).value.decode = CurrentRectangleIndex.defect security order rationalMatrix
      (finProdFinEquiv.symm output) (finProdFinEquiv.symm input))
    (point : CurrentRectangleIndex.Point security order) :
    (((run security order steps entry).value.get (CurrentRectangleIndex.encode security order point).1).get
      (CurrentRectangleIndex.encode security order point).2).decode =
      linearIteration rationalMatrix (CalibrationMatrixApproximation.rhs security order) steps point := by
  exact BinaryRectangleIteration.actual_value security order steps rationalMatrix (current security order entry).matrix (current security order entry).rhs
    (fun output input => by rw [matrix_value, hentry]) (fun output => by rw [rhs_value, rhs_flat]) point

end
end CurrentAFT.BinaryRectangleMaterialization

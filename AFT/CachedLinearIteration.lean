import AFT.ActualInverseEntryProgram

/-! # Materialized rational matrix iteration

Each iteration stores a complete vector before the next one begins. Thus
querying one entry never recursively recomputes the previous vector.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

def cachedMatrix (colors : ℕ) (matrix : Fin colors → Fin colors → ℚ) : Vector (Vector ℚ colors) colors :=
  Vector.ofFn (fun output => Vector.ofFn (matrix output))

def cachedMatrixApply {colors : ℕ} (matrix : Vector (Vector ℚ colors) colors)
    (profile : Vector ℚ colors) : Vector ℚ colors :=
  Vector.ofFn (fun output => ∑ input,(matrix.get output).get input*profile.get input)

def cachedLinearIteration {colors : ℕ} (matrix : Vector (Vector ℚ colors) colors)
    (rhs : Vector ℚ colors) : ℕ → Vector ℚ colors
  | 0 => Vector.ofFn (fun _ => 0)
  | steps+1 =>
      let previous := cachedLinearIteration matrix rhs steps
      let applied := cachedMatrixApply matrix previous
      Vector.ofFn (fun output => rhs.get output-applied.get output)

theorem cachedLinearIteration_get (colors : ℕ) (matrix : Fin colors → Fin colors → ℚ)
    (rhs : Fin colors → ℚ) (steps : ℕ) (output : Fin colors) :
    (cachedLinearIteration (cachedMatrix colors matrix) (Vector.ofFn rhs) steps).get output=
      linearIteration matrix rhs steps output := by
  induction steps generalizing output with
  | zero => simp [cachedLinearIteration,linearIteration]
  | succ steps ih =>
    simp only [cachedLinearIteration,cachedMatrixApply,Vector.get_ofFn,cachedMatrix,linearIteration,
      Pi.sub_apply,matrixApply]
    apply congrArg (fun value => rhs output-value)
    apply Finset.sum_congr rfl
    intro input _
    exact congrArg (fun value => matrix output input*value) (ih input)

/-- Counts scalar additions/subtractions and multiplications in all stored
matrix-vector iterations, once the matrix and right-hand side are loaded. -/
def cachedIterationWork (colors steps : ℕ) : ℕ := steps*(2*colors^2+colors)

theorem cachedIterationWork_step (colors steps : ℕ) :
    cachedIterationWork colors (steps+1)=cachedIterationWork colors steps+2*colors^2+colors := by
  unfold cachedIterationWork
  ring

end AFT.RationalNumerics

namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- All matrix entries are stored before iteration. The sole loop state is
one materialized rational vector. -/
def actualCachedInverseProgram (constant n input steps output : ℕ) : ℚ :=
  let colors := (ParameterProgram.modulus n).value
  let matrix := cachedMatrix colors (fun out inp => actualPreconditionedMatrixProgram constant n inp.val out.val)
  let rhs := Vector.ofFn (fun out : Fin colors => actualRankInverseProgram constant n input out.val)
  let result := cachedLinearIteration matrix rhs steps
  if h : output<colors then result.get ⟨output,h⟩ else 0

theorem actualCachedInverseProgram_eq (constant n input steps output : ℕ)
    (hout : output<(ParameterProgram.modulus n).value) :
    actualCachedInverseProgram constant n input steps output=actualInverseIterationProgram constant n input steps output := by
  simp only [actualCachedInverseProgram,dif_pos hout,cachedLinearIteration_get]
  have hh (steps : ℕ) (out : Fin (ParameterProgram.modulus n).value) :
      linearIteration (fun o i : Fin (ParameterProgram.modulus n).value => actualPreconditionedMatrixProgram constant n i.val o.val)
        (fun o => actualRankInverseProgram constant n input o.val) steps out=
      actualInverseIterationProgram constant n input steps out.val := by
    induction steps generalizing out with
    | zero => rfl
    | succ steps ih =>
      simp only [linearIteration,actualInverseIterationProgram,Pi.sub_apply,matrixApply]
      congr 1
      simp_rw [ih]
      exact Fin.sum_univ_eq_sum_range (fun middle => actualPreconditionedMatrixProgram constant n middle out.val*
        actualInverseIterationProgram constant n input steps middle) _
  exact hh steps ⟨output,hout⟩

noncomputable section
open scoped Topology
local instance cachedIterationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem actual_cached_inverse_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
        operator.toLinearMap=actualResponse (constant : ℝ) n ∧
        ∀ (input output : Fin (Parameters.modulus n)),
          |(actualCachedInverseProgram constant n input.val n output.val : ℝ)-operator.symm (Pi.single input 1) output|≤
            actualInverseEntryError n := by
  filter_upwards [actual_inverse_entry_program_eventually constant hc] with n hh
  obtain ⟨operator,hop,he⟩ := hh
  refine ⟨operator,hop,?_⟩
  intro input output
  rw [actualCachedInverseProgram_eq _ _ _ _ _ (by simpa only [ParameterProgram.modulus_value] using output.isLt)]
  exact he input output

/-- The actual V7 palette q≤2n^40 gives a polynomial count of arithmetic
operations in the stored iteration. Bit lengths are a separate obligation. -/
theorem actualCachedInverseProgram_iteration_work (n : ℕ) (hn : 2≤n) :
    cachedIterationWork (ParameterProgram.modulus n).value n≤10*n^81 := by
  have hq : (ParameterProgram.modulus n).value≤2*n^40 := by
    rw [ParameterProgram.modulus_value]
    simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2
  unfold cachedIterationWork
  have hh : n*(2*((ParameterProgram.modulus n).value)^2+(ParameterProgram.modulus n).value)≤
      n*(2*(2*n^40)^2+2*n^40) := by gcongr
  apply hh.trans
  have hp : n^41≤n^81 := Nat.pow_le_pow_right (by omega : 1≤n) (by decide)
  nlinarith

end
end AFT.V7Calibration

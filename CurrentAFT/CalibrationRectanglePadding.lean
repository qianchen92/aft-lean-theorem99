import AFT.RationalLinearIteration

/-! # Zero padding of the calibration defect in rectangular storage

The full response is the identity on unused rectangular coordinates.
Equivalently its defect, right-hand side, and every iterate vanish there.
This exact data statement allows rectangular array reads without changing
any joint safe-palette coordinate of the calibration algorithm.
-/
namespace CurrentAFT.CalibrationRectanglePadding
open AFT RationalNumerics
open scoped BigOperators

variable {Small Large : Type*}

def extend {Scalar : Type*} [Zero Scalar] (decode : Large → Option Small)
    (table : Small → Scalar) (point : Large) : Scalar :=
  (decode point).elim 0 table

def defect {Scalar : Type*} [Zero Scalar] (decode : Large → Option Small)
    (matrix : Small → Small → Scalar) (output input : Large) : Scalar :=
  (decode output).elim 0 (fun out => (decode input).elim 0 (matrix out))

section
variable [Fintype Small] [Fintype Large]
variable (encode : Small ↪ Large) (decode : Large → Option Small)
variable (hdecode : ∀ point small, decode point = some small ↔ point = encode small)
include encode hdecode

omit [Fintype Small] [Fintype Large] in
theorem decode_encode (point : Small) : decode (encode point) = some point :=
  (hdecode _ _).mpr rfl

theorem sum_extend {Scalar : Type*} [AddCommMonoid Scalar] (table : Small → Scalar) :
    (∑ point, extend decode table point) = ∑ point, table point := by
  have hsubset : Finset.univ.map encode ⊆ (Finset.univ : Finset Large) := Finset.subset_univ _
  have hsum := Finset.sum_subset hsubset (f := extend decode table) (by
    intro point _ hnot
    have hn : decode point = none := by
      cases hd : decode point with
      | none => rfl
      | some small =>
        have hp := (hdecode point small).mp hd
        subst point
        exact False.elim (hnot (Finset.mem_map.mpr ⟨small, Finset.mem_univ _, rfl⟩))
    simp only [extend, hn, Option.elim_none])
  rw [← hsum, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro point _
  simp only [extend, decode_encode encode decode hdecode, Option.elim_some]

theorem matrixApply_extend (matrix : Small → Small → ℚ) (table : Small → ℚ) :
    matrixApply (defect decode matrix) (extend decode table) = extend decode (matrixApply matrix table) := by
  funext output
  cases ho : decode output with
  | none => simp only [matrixApply, defect, extend, ho, Option.elim_none, zero_mul, Finset.sum_const_zero]
  | some small =>
    simp only [matrixApply, defect, extend, ho, Option.elim_some]
    have he (input : Large) :
        (decode input).elim 0 (matrix small) * (decode input).elim 0 table =
          extend decode (fun point => matrix small point * table point) input := by
      cases hi : decode input <;> simp [extend, hi]
    simp_rw [he]
    exact sum_extend encode decode hdecode _

theorem linearIteration_extend (matrix : Small → Small → ℚ) (rhs : Small → ℚ) (steps : ℕ) :
    linearIteration (defect decode matrix) (extend decode rhs) steps =
      extend decode (linearIteration matrix rhs steps) := by
  induction steps with
  | zero =>
    funext point
    cases hd : decode point <;> simp [linearIteration, extend, hd]
  | succ steps ih =>
    rw [linearIteration, ih, matrixApply_extend encode decode hdecode]
    funext point
    cases hd : decode point <;> simp [linearIteration, extend, hd]

theorem linearIteration_at (matrix : Small → Small → ℚ) (rhs : Small → ℚ) (steps : ℕ) (point : Small) :
    linearIteration (defect decode matrix) (extend decode rhs) steps (encode point) =
      linearIteration matrix rhs steps point := by
  rw [linearIteration_extend encode decode hdecode]
  simp only [extend, decode_encode encode decode hdecode, Option.elim_some]

theorem linearIteration_unused (matrix : Small → Small → ℚ) (rhs : Small → ℚ)
    (steps : ℕ) (point : Large) (hpoint : decode point = none) :
    linearIteration (defect decode matrix) (extend decode rhs) steps point = 0 := by
  rw [linearIteration_extend encode decode hdecode]
  simp only [extend, hpoint, Option.elim_none]

end
end CurrentAFT.CalibrationRectanglePadding

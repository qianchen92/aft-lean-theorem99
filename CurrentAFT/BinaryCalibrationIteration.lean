import CurrentAFT.CalibrationMatrixApproximation

/-! # Polynomial bit work for stored rational calibration iteration

The reused binary program performs every matrix read, multiplication, sum,
and cached vector update. A common denominator for the fixed stored matrix
and right-hand side gives a height bound linear in the iteration count.
These bounds concern the genuine program, not an assumed runtime field.
-/
namespace CurrentAFT.BinaryCalibrationIteration
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open Polynomial

noncomputable def heightPolynomial (count bits steps : Polynomial ℕ) : Polynomial ℕ :=
  steps * ((3 * (count^2 + count) + 1) * bits + count + 1)

noncomputable def primitivePolynomial (bits : Polynomial ℕ) : Polynomial ℕ := 10000000 * (bits + 2)^3

noncomputable def workPolynomial (count bits steps : Polynomial ℕ) : Polynomial ℕ :=
  let B := bits + heightPolynomial count bits steps
  let D := (count + 1) * (2 * B + 1)
  let row := count * (10 * count + 13 + primitivePolynomial B + primitivePolynomial D + 2) + 2
  let step := count * (row + 2) + 2 + count * (6 * count + 13 + 2 * primitivePolynomial D) + 5
  steps * step + 2 * count + 2

theorem heightPolynomial_eval (count bits steps : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial count bits steps).eval security =
      steps.eval security * ((3 * ((count.eval security)^2 + count.eval security) + 1) *
        bits.eval security + count.eval security + 1) := by
  simp [heightPolynomial]

theorem workPolynomial_eval (count bits steps : Polynomial ℕ) (security : ℕ) :
    (workPolynomial count bits steps).eval security =
      steps.eval security * iterationWorkStep (count.eval security) (bits.eval security) (steps.eval security) +
        2 * count.eval security + 2 := by
  simp [workPolynomial, primitivePolynomial, heightPolynomial, iterationWorkStep,
    iterationBits, matrixApplyWork, matrixRowWork, primitiveWorkBound]

theorem iterationWorkStep_mono_count {count larger bits limit : ℕ} (hcount : count ≤ larger) :
    iterationWorkStep count bits limit ≤ iterationWorkStep larger bits limit := by
  unfold iterationWorkStep iterationBits matrixApplyWork matrixRowWork primitiveWorkBound
  gcongr

theorem polynomial_work (security count steps : ℕ) (countBound bitsBound stepsBound : Polynomial ℕ)
    (matrix : Vector (Vector RationalBits count) count) (rhs : Vector RationalBits count)
    (hcount : count ≤ countBound.eval security) (hsteps : steps ≤ stepsBound.eval security)
    (hmatrix : ∀ output input, HeightBound ((matrix.get output).get input).decode (bitsBound.eval security))
    (hrhs : ∀ output, HeightBound (rhs.get output).decode (bitsBound.eval security)) :
    (iteration matrix rhs steps).work ≤ (workPolynomial countBound bitsBound stepsBound).eval security := by
  apply (iteration_work matrix rhs (bitsBound.eval security) (stepsBound.eval security) steps
    hmatrix hrhs hsteps).trans
  rw [workPolynomial_eval]
  have hstep := iterationWorkStep_mono_count (bits := bitsBound.eval security)
    (limit := stepsBound.eval security) hcount
  gcongr

theorem polynomial_height (security count steps : ℕ) (countBound bitsBound stepsBound : Polynomial ℕ)
    (matrix : Vector (Vector RationalBits count) count) (rhs : Vector RationalBits count)
    (hcount : count ≤ countBound.eval security) (hsteps : steps ≤ stepsBound.eval security)
    (hmatrix : ∀ output input, HeightBound ((matrix.get output).get input).decode (bitsBound.eval security))
    (hrhs : ∀ output, HeightBound (rhs.get output).decode (bitsBound.eval security)) (output : Fin count) :
    HeightBound ((iteration matrix rhs steps).data.get output).decode
      ((heightPolynomial countBound bitsBound stepsBound).eval security) := by
  rw [iteration_value]
  have h := linearIteration_height (fun out inp => ((matrix.get out).get inp).decode)
    (fun out => (rhs.get out).decode) (bitsBound.eval security) steps hmatrix hrhs output
  simp only [Fintype.card_fin] at h
  apply h.mono
  rw [heightPolynomial_eval]
  gcongr

end CurrentAFT.BinaryCalibrationIteration

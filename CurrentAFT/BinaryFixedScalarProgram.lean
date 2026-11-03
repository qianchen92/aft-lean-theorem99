import AFT.BinaryStoredScalar
import CurrentAFT.BinaryCalibrationIteration

/-! # Derived bit bounds for fixed-order stored arithmetic syntax

Only the fixed calibration order determines this syntax and its encoded
literals. Security-dependent values enter through executed binary leaves.
All intermediate heights are derived from the syntax, not supplied as a
runtime assumption.
-/
namespace CurrentAFT.BinaryFixedScalarProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 600000

variable {Leaf : Type*}

def literalBound : ScalarProgram Leaf → ℕ
  | .rational value => rationalLiteralHeight value
  | .atom _ => 0
  | .add first second => max (literalBound first) (literalBound second)
  | .multiply first second => max (literalBound first) (literalBound second)
  | .negate term => literalBound term
  | .inverse term => literalBound term

theorem literals_mono (program : ScalarProgram Leaf) {first second : ℕ}
    (hle : first ≤ second) (hfirst : program.literalsBounded first) : program.literalsBounded second := by
  induction program with
  | rational value => exact hfirst.trans hle
  | atom _ => trivial
  | add first second hf hs => exact ⟨hf hfirst.1, hs hfirst.2⟩
  | multiply first second hf hs => exact ⟨hf hfirst.1, hs hfirst.2⟩
  | negate term ih => exact ih hfirst
  | inverse term ih => exact ih hfirst

theorem literals_bounded (program : ScalarProgram Leaf) : program.literalsBounded (literalBound program) := by
  induction program with
  | rational value => exact le_refl _
  | atom _ => trivial
  | add first second hf hs =>
    exact ⟨literals_mono first (Nat.le_max_left _ _) hf, literals_mono second (Nat.le_max_right _ _) hs⟩
  | multiply first second hf hs =>
    exact ⟨literals_mono first (Nat.le_max_left _ _) hf, literals_mono second (Nat.le_max_right _ _) hs⟩
  | negate term ih => exact ih
  | inverse term ih => exact ih

def height (program : StoredScalarProgram Leaf RationalBits) (leafBits : ℕ) : ℕ :=
  (program.meaning RationalBits.decode).nodes * (leafBits + literalBound (program.meaning RationalBits.decode) + 1)

def work (program : StoredScalarProgram Leaf RationalBits) (leafBits leafWork : ℕ) : ℕ :=
  (program.meaning RationalBits.decode).nodes * (leafWork + primitiveWorkBound (height program leafBits) + 1)

theorem evaluation_height (program : StoredScalarProgram Leaf RationalBits)
    (leaf : Leaf → CountedValue RationalBits) (bits : ℕ)
    (hleaf : ∀ code, HeightBound (leaf code).value.decode bits)
    (value : ℚ) (hvalue : value ∈ (program.meaning RationalBits.decode).evaluationValues
      (fun code => (leaf code).value.decode)) : HeightBound value (height program bits) := by
  have h := (program.meaning RationalBits.decode).evaluationValues_height
    (fun code => (leaf code).value.decode) (fun _ => bits) hleaf value hvalue
  apply h.mono
  exact ScalarProgram.heightBudget_le _ (bits + literalBound (program.meaning RationalBits.decode))
    (fun _ => Nat.le_add_right _ _) _
    (literals_mono _ (Nat.le_add_left _ _) (literals_bounded _))

theorem run_height (program : StoredScalarProgram Leaf RationalBits)
    (leaf : Leaf → CountedValue RationalBits) (bits : ℕ)
    (hleaf : ∀ code, HeightBound (leaf code).value.decode bits) :
    HeightBound (program.binaryRun leaf).value.decode (height program bits) := by
  rw [StoredScalarProgram.binaryRun_value]
  exact evaluation_height program leaf bits hleaf _ (ScalarProgram.run_mem_evaluationValues _ _)

theorem run_work (program : StoredScalarProgram Leaf RationalBits)
    (leaf : Leaf → CountedValue RationalBits) (bits budget : ℕ)
    (hleaf : ∀ code, HeightBound (leaf code).value.decode bits)
    (hwork : ∀ code, (leaf code).work ≤ budget) :
    (program.binaryRun leaf).work ≤ work program bits budget :=
  StoredScalarProgram.binaryRun_work leaf program (height program bits) budget hwork
    (evaluation_height program leaf bits hleaf)

noncomputable def heightPolynomial (program : StoredScalarProgram Leaf RationalBits)
    (leafBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (program.meaning RationalBits.decode).nodes *
    (leafBits + Polynomial.C (literalBound (program.meaning RationalBits.decode)) + 1)

noncomputable def workPolynomial (program : StoredScalarProgram Leaf RationalBits)
    (leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (program.meaning RationalBits.decode).nodes *
    (leafWork + BinaryCalibrationIteration.primitivePolynomial (heightPolynomial program leafBits) + 1)

theorem heightPolynomial_eval (program : StoredScalarProgram Leaf RationalBits)
    (leafBits : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial program leafBits).eval security = height program (leafBits.eval security) := by
  simp [heightPolynomial, height]

theorem workPolynomial_eval (program : StoredScalarProgram Leaf RationalBits)
    (leafBits leafWork : Polynomial ℕ) (security : ℕ) :
    (workPolynomial program leafBits leafWork).eval security = work program (leafBits.eval security) (leafWork.eval security) := by
  simp [workPolynomial, BinaryCalibrationIteration.primitivePolynomial, heightPolynomial_eval, work, primitiveWorkBound]

end CurrentAFT.BinaryFixedScalarProgram

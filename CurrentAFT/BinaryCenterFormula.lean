import CurrentAFT.BinaryProposalMetadata
import AFT.ScalarCompilationResources

/-! # Executed scalar formula for the current center correction -/
namespace CurrentAFT.BinaryCenterFormula
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | colors | legs | population | activation | safe | anchor
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  let colors : ScalarProgram Leaf := .atom .colors
  let legs : ScalarProgram Leaf := .atom .legs
  let population : ScalarProgram Leaf := .atom .population
  let rate : ScalarProgram Leaf := .atom .activation
  let remaining := .add (.add population (.negate legs)) (.negate colors)
  let compensation := .multiply (.multiply legs rate) (.inverse remaining)
  .add (.multiply (.add (.rational 1) compensation) (.atom .safe))
    (.negate (.multiply compensation (.atom .anchor)))

theorem expression_literals : expression.LiteralBound 1 := by
  norm_num [expression, ScalarProgram.LiteralBound, RationalLiteralBound]

def leaf (metadata : BinaryProposalMetadata.Encoded) (rate safe anchor : RationalBits) : Leaf → RationalBits
  | .colors => metadata.colors
  | .legs => metadata.legs
  | .population => metadata.population
  | .activation => rate
  | .safe => safe
  | .anchor => anchor

def read (values : Leaf → RationalBits) (code : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values code)
  ⟨result.data, result.work+1⟩

def current (metadata : BinaryProposalMetadata.Encoded) (rate safe anchor : RationalBits) : RationalResult :=
  let result := expression.compileBinaryRun (read (leaf metadata rate safe anchor))
  ⟨result.value, result.work+1⟩

theorem current_value (metadata : BinaryProposalMetadata.Encoded) (rate safe anchor : RationalBits) :
    (current metadata rate safe anchor).data.decode =
      (1+metadata.legs.decode*rate.decode/(metadata.population.decode-metadata.legs.decode-metadata.colors.decode))*safe.decode-
        metadata.legs.decode*rate.decode/(metadata.population.decode-metadata.legs.decode-metadata.colors.decode)*anchor.decode := by
  simp only [current, ScalarProgram.compileBinaryRun_value, read, RationalBits.copy_value,
    expression, leaf, ScalarProgram.run, div_eq_mul_inv, sub_eq_add_neg]

def height (bound : ℕ) : ℕ := expression.nodes*(bound+3)
def work (bound : ℕ) : ℕ := expression.nodes*
  (smallRationalEncodingWork 1+(4*bound+9)+primitiveWorkBound (height bound)+2)+2

theorem current_bounds (metadata : BinaryProposalMetadata.Encoded) (rate safe anchor : RationalBits) (bound : ℕ)
    (hq : HeightBound metadata.colors.decode bound) (hl : HeightBound metadata.legs.decode bound)
    (hp : HeightBound metadata.population.decode bound) (hr : HeightBound rate.decode bound)
    (hs : HeightBound safe.decode bound) (ha : HeightBound anchor.decode bound) :
    HeightBound (current metadata rate safe anchor).data.decode (height bound) ∧
      (current metadata rate safe anchor).work ≤ work bound := by
  let values := leaf metadata rate safe anchor
  have hv (code : Leaf) : HeightBound (values code).decode bound := by
    cases code <;> assumption
  have hh (code : Leaf) : HeightBound (read values code).value.decode bound := by
    rw [read, RationalBits.copy_value]
    exact hv code
  have hw (code : Leaf) : (read values code).work ≤ 4*bound+9 := by
    have hc := RationalBits.copy_work (values code) bound (hv code)
    change (RationalBits.copy (values code)).work+1 ≤ _
    omega
  have w := expression.compileBinaryRun_work_of_bounds (read values) 1 bound (4*bound+9) expression_literals hw hh
  have h := expression.run_height (fun code => (read values code).value.decode) (fun _ => bound) hh
  have hb := expression.heightBudget_le (fun _ => bound) (bound+2) (fun _ => Nat.le_add_right _ _)
    (ScalarProgram.literalsBounded_mono expression_literals.literalsBounded (Nat.le_add_left _ _))
  constructor
  · change HeightBound (expression.compileBinaryRun (read values)).value.decode _
    rw [ScalarProgram.compileBinaryRun_value]
    exact h.mono (hb.trans_eq (by unfold height; congr 1))
  · change (expression.compileBinaryRun (read values)).work+1 ≤ _
    unfold work height
    simp only [Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] at w ⊢
    omega

noncomputable def heightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := Polynomial.C expression.nodes*(bound+3)
noncomputable def workPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(smallRationalEncodingPolynomial 1+(4*bound+9)+
    primitiveWorkPolynomial (heightPolynomial bound)+2)+2

theorem heightPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial bound).eval security = height (bound.eval security) := by
  simp only [heightPolynomial, height, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_ofNat]

theorem workPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (workPolynomial bound).eval security = work (bound.eval security) := by
  simp only [workPolynomial, work, smallRationalEncodingPolynomial_eval, primitiveWorkPolynomial_eval,
    heightPolynomial_eval, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one]

end CurrentAFT.BinaryCenterFormula

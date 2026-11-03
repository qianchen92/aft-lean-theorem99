import CurrentAFT.BinaryMassLiftFormula

/-! # Literal compiled arithmetic of the original projected seed density -/
namespace CurrentAFT.BinarySeedDensityFormula
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | shifted | fringe | total | safe | center
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  .multiply
    (.add (.add (.add (.atom .shifted) (.negate (.atom .fringe)))
      (.multiply (.atom .total) (.atom .safe))) (.negate (.atom .safe)))
    (.inverse (.atom .center))

theorem expression_literals : expression.LiteralBound 1 := by trivial

def leaf (shifted fringe total safe center : RationalBits) : Leaf→RationalBits
  | .shifted => shifted
  | .fringe => fringe
  | .total => total
  | .safe => safe
  | .center => center

def read (values : Leaf→RationalBits) (code : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values code)
  ⟨result.data,result.work+1⟩

def current (shifted fringe total safe center : RationalBits) : RationalResult :=
  let result := expression.compileBinaryRun (read (leaf shifted fringe total safe center))
  ⟨result.value,result.work+1⟩

theorem current_value (shifted fringe total safe center : RationalBits) :
    (current shifted fringe total safe center).data.decode=
      (shifted.decode-fringe.decode+total.decode*safe.decode-safe.decode)/center.decode := by
  simp only [current, ScalarProgram.compileBinaryRun_value, read, RationalBits.copy_value,
    expression, leaf, ScalarProgram.run, div_eq_mul_inv, sub_eq_add_neg]

def height (bound : ℕ) := expression.nodes*(bound+3)
def work (bound : ℕ) := expression.nodes*(smallRationalEncodingWork 1+(4*bound+9)+primitiveWorkBound (height bound)+2)+2

theorem current_bounds (shifted fringe total safe center : RationalBits) (bound : ℕ)
    (hs : HeightBound shifted.decode bound) (hf : HeightBound fringe.decode bound)
    (ht : HeightBound total.decode bound) (hb : HeightBound safe.decode bound) (hc : HeightBound center.decode bound) :
    HeightBound (current shifted fringe total safe center).data.decode (height bound) ∧
      (current shifted fringe total safe center).work≤work bound := by
  let values := leaf shifted fringe total safe center
  have hv (code : Leaf) : HeightBound (values code).decode bound := by cases code <;> assumption
  have hh (code : Leaf) : HeightBound (read values code).value.decode bound := by
    rw [read, RationalBits.copy_value]
    exact hv code
  have hw (code : Leaf) : (read values code).work≤4*bound+9 := by
    have h := RationalBits.copy_work (values code) bound (hv code)
    change _+1≤_
    omega
  have w := expression.compileBinaryRun_work_of_bounds (read values) 1 bound (4*bound+9) expression_literals hw hh
  have h := expression.run_height (fun code => (read values code).value.decode) (fun _ => bound) hh
  have hb := expression.heightBudget_le (fun _ => bound) (bound+2) (fun _ => Nat.le_add_right _ _)
    (ScalarProgram.literalsBounded_mono expression_literals.literalsBounded (Nat.le_add_left _ _))
  constructor
  · change HeightBound (expression.compileBinaryRun (read values)).value.decode _
    rw [ScalarProgram.compileBinaryRun_value]
    exact h.mono (hb.trans_eq (by unfold height; congr 1))
  · change (expression.compileBinaryRun (read values)).work+1≤_
    unfold work height
    simp only [Nat.mul_one,Nat.add_assoc,Nat.reduceAdd] at w ⊢
    omega

noncomputable def heightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := Polynomial.C expression.nodes*(bound+3)
noncomputable def workPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(smallRationalEncodingPolynomial 1+(4*bound+9)+primitiveWorkPolynomial (heightPolynomial bound)+2)+2

theorem heightPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial bound).eval security=height (bound.eval security) := by
  simp only [heightPolynomial,height,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_ofNat]

theorem workPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (workPolynomial bound).eval security=work (bound.eval security) := by
  simp only [workPolynomial,work,smallRationalEncodingPolynomial_eval,primitiveWorkPolynomial_eval,
    heightPolynomial_eval,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]

end CurrentAFT.BinarySeedDensityFormula

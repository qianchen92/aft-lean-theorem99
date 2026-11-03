import AFT.ParametricOrderedTable
import AFT.CountedGaussianArithmetic
import AFT.RationalHeight

/-! # Literal work and intermediate rational heights of scalar expressions -/
namespace AFT.RationalNumerics

/-- A computable bound for the height of a rational literal. -/
def rationalLiteralHeight (value : ℚ) : ℕ := value.num.natAbs.size+value.den.size

theorem rationalLiteralHeight_bound (value : ℚ) : HeightBound value (rationalLiteralHeight value) := by
  constructor
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

namespace ScalarProgram
variable {Scalar : Type*}

def nodes : ScalarProgram Scalar → ℕ
  | .rational _ => 1
  | .atom _ => 1
  | .add first second => first.nodes+second.nodes+1
  | .multiply first second => first.nodes+second.nodes+1
  | .negate term => term.nodes+1
  | .inverse term => term.nodes+1

/-- Each child is computed once and stored before the parent operation. -/
def countedRun (leaf : Scalar → GaussianArithmetic) : ScalarProgram Scalar → GaussianArithmetic
  | .rational value => .literal value
  | .atom code => leaf code
  | .add first second => (first.countedRun leaf).add (second.countedRun leaf)
  | .multiply first second => (first.countedRun leaf).mul (second.countedRun leaf)
  | .negate term => let result := term.countedRun leaf;⟨-result.value,result.work+1⟩
  | .inverse term => let result := term.countedRun leaf;⟨result.value⁻¹,result.work+1⟩

theorem countedRun_value (leaf : Scalar → GaussianArithmetic) (program : ScalarProgram Scalar) :
    (program.countedRun leaf).value=program.run (fun code => (leaf code).value) := by
  induction program <;> simp_all only [countedRun,run,GaussianArithmetic.literal,
    GaussianArithmetic.add,GaussianArithmetic.mul]

theorem countedRun_work (leaf : Scalar → GaussianArithmetic) (bound : ℕ)
    (hbound : ∀ code,(leaf code).work≤bound) (program : ScalarProgram Scalar) :
    (program.countedRun leaf).work≤program.nodes*(bound+1) := by
  induction program with
  | rational value => simp only [countedRun,GaussianArithmetic.literal,nodes]; omega
  | atom code => simpa only [countedRun,nodes,one_mul] using (hbound code).trans (Nat.le_succ _)
  | add first second hf hs => simp only [countedRun,GaussianArithmetic.add,nodes];nlinarith
  | multiply first second hf hs => simp only [countedRun,GaussianArithmetic.mul,nodes];nlinarith
  | negate term ht => simp only [countedRun,nodes];nlinarith
  | inverse term ht => simp only [countedRun,nodes];nlinarith

/-- The literal heights are included rather than treated as unit-cost constants. -/
def heightBudget (leafHeight : Scalar → ℕ) : ScalarProgram Scalar → ℕ
  | .rational value => rationalLiteralHeight value
  | .atom code => leafHeight code
  | .add first second => first.heightBudget leafHeight+second.heightBudget leafHeight+1
  | .multiply first second => first.heightBudget leafHeight+second.heightBudget leafHeight
  | .negate term => term.heightBudget leafHeight
  | .inverse term => term.heightBudget leafHeight

theorem run_height (leaf : Scalar → ℚ) (leafHeight : Scalar → ℕ)
    (hbound : ∀ code,HeightBound (leaf code) (leafHeight code)) (program : ScalarProgram Scalar) :
    HeightBound (program.run leaf) (program.heightBudget leafHeight) := by
  induction program with
  | rational value => exact rationalLiteralHeight_bound value
  | atom code => exact hbound code
  | add first second hf hs => exact hf.add hs
  | multiply first second hf hs => exact hf.mul hs
  | negate term ht => exact ht.neg
  | inverse term ht => exact ht.inv

/-- Proof-side list of all scalar-node results visited by `countedRun`.
Internal leaf computations use their separate actual-program height bounds. -/
def evaluationValues (leaf : Scalar → ℚ) : ScalarProgram Scalar → List ℚ
  | .rational value => [value]
  | .atom code => [leaf code]
  | .add first second => first.evaluationValues leaf ++ second.evaluationValues leaf ++ [first.run leaf+second.run leaf]
  | .multiply first second => first.evaluationValues leaf ++ second.evaluationValues leaf ++ [first.run leaf*second.run leaf]
  | .negate term => term.evaluationValues leaf ++ [-term.run leaf]
  | .inverse term => term.evaluationValues leaf ++ [(term.run leaf)⁻¹]

/-- Both operands and every intermediate scalar result have the displayed
bound, not just the final rational answer. -/
theorem evaluationValues_height (leaf : Scalar → ℚ) (leafHeight : Scalar → ℕ)
    (hbound : ∀ code,HeightBound (leaf code) (leafHeight code)) (program : ScalarProgram Scalar)
    (value : ℚ) (hvalue : value∈program.evaluationValues leaf) :
    HeightBound value (program.heightBudget leafHeight) := by
  induction program with
  | rational literal =>
    simp only [evaluationValues,List.mem_singleton] at hvalue
    subst value
    exact rationalLiteralHeight_bound literal
  | atom code =>
    simp only [evaluationValues,List.mem_singleton] at hvalue
    subst value
    exact hbound code
  | add first second hf hs =>
    simp only [evaluationValues,List.mem_append,List.mem_singleton] at hvalue
    rcases hvalue with (hv|hv)|hv
    · exact (hf hv).mono (by simp only [heightBudget];omega)
    · exact (hs hv).mono (by simp only [heightBudget];omega)
    · subst value
      exact (run_height leaf leafHeight hbound first).add (run_height leaf leafHeight hbound second)
  | multiply first second hf hs =>
    simp only [evaluationValues,List.mem_append,List.mem_singleton] at hvalue
    rcases hvalue with (hv|hv)|hv
    · exact (hf hv).mono (Nat.le_add_right _ _)
    · exact (hs hv).mono (Nat.le_add_left _ _)
    · subst value
      exact (run_height leaf leafHeight hbound first).mul (run_height leaf leafHeight hbound second)
  | negate term ht =>
    simp only [evaluationValues,List.mem_append,List.mem_singleton] at hvalue
    rcases hvalue with hv|hv
    · exact ht hv
    · subst value
      exact (run_height leaf leafHeight hbound term).neg
  | inverse term ht =>
    simp only [evaluationValues,List.mem_append,List.mem_singleton] at hvalue
    rcases hvalue with hv|hv
    · exact ht hv
    · subst value
      exact (run_height leaf leafHeight hbound term).inv

def literalsBounded (bits : ℕ) : ScalarProgram Scalar → Prop
  | .rational value => rationalLiteralHeight value≤bits
  | .atom _ => True
  | .add first second => first.literalsBounded bits ∧ second.literalsBounded bits
  | .multiply first second => first.literalsBounded bits ∧ second.literalsBounded bits
  | .negate term => term.literalsBounded bits
  | .inverse term => term.literalsBounded bits

theorem heightBudget_le (leafHeight : Scalar → ℕ) (bits : ℕ) (hbound : ∀ code,leafHeight code≤bits)
    (program : ScalarProgram Scalar) (hliterals : program.literalsBounded bits) :
    program.heightBudget leafHeight≤program.nodes*(bits+1) := by
  induction program with
  | rational value => exact hliterals.trans (by simp only [nodes,one_mul];omega)
  | atom code => simpa only [heightBudget,nodes,one_mul] using (hbound code).trans (Nat.le_succ _)
  | add first second hf hs =>
    have hf := hf hliterals.1
    have hs := hs hliterals.2
    simp only [heightBudget,nodes]
    nlinarith
  | multiply first second hf hs =>
    have hf := hf hliterals.1
    have hs := hs hliterals.2
    simp only [heightBudget,nodes]
    nlinarith
  | negate term ht =>
    have ht := ht hliterals
    simp only [heightBudget,nodes]
    nlinarith
  | inverse term ht =>
    have ht := ht hliterals
    simp only [heightBudget,nodes]
    nlinarith

end ScalarProgram
end AFT.RationalNumerics

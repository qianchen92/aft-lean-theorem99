import AFT.StoredScalarEvaluation
import AFT.BinaryRationalOperations
import AFT.BinaryRationalLiterals

/-! Actual binary implementation of every scalar arithmetic node. There is
no rational primitive or unproved primitive-cost premise in this evaluator. -/
namespace AFT.RationalNumerics
open RationalRejectionProgram BinaryArithmetic

/-- Runtime calls only the Boolean-list algorithms, including actual gcd
normalization after addition and multiplication. -/
def binaryOperations : RationalOperations RationalBits where
  add first second :=
    let result := RationalBits.add first second
    ⟨result.data,result.work⟩
  multiply first second :=
    let result := RationalBits.multiply first second
    ⟨result.data,result.work⟩
  negate input :=
    let result := RationalBits.negate input
    ⟨result.data,result.work⟩
  inverse input :=
    let result := RationalBits.inverse input
    ⟨result.data,result.work⟩

theorem binaryOperations_correct : binaryOperations.Correct RationalBits.decode where
  add := RationalBits.add_value
  multiply := RationalBits.multiply_value
  negate := RationalBits.negate_value
  inverse := RationalBits.inverse_value

namespace StoredScalarProgram
variable {Scalar : Type*}

def binaryRun (leaf : Scalar → CountedValue RationalBits)
    (program : StoredScalarProgram Scalar RationalBits) : CountedValue RationalBits :=
  program.run binaryOperations leaf

theorem binaryRun_value (leaf : Scalar → CountedValue RationalBits)
    (program : StoredScalarProgram Scalar RationalBits) :
    (program.binaryRun leaf).value.decode=
      (program.meaning RationalBits.decode).run (fun code => (leaf code).value.decode) :=
  program.run_value binaryOperations RationalBits.decode binaryOperations_correct leaf

/-- Polynomial bit-operation overhead, with primitive implementation and
normalization fully instantiated. `hvalues` is the existing operand-height
invariant for this actual syntax, not an assumed operation runtime. -/
theorem binaryRun_work (leaf : Scalar → CountedValue RationalBits)
    (program : StoredScalarProgram Scalar RationalBits) (bits leafWork : ℕ)
    (hleaf : ∀ code,(leaf code).work ≤ leafWork)
    (hvalues : ∀ value∈(program.meaning RationalBits.decode).evaluationValues
      (fun code => (leaf code).value.decode),HeightBound value bits) :
    (program.binaryRun leaf).work ≤ (program.meaning RationalBits.decode).nodes*
      (leafWork+RationalBits.primitiveWorkBound bits+1) := by
  apply program.run_work binaryOperations RationalBits.decode binaryOperations_correct leaf
    bits (leafWork+RationalBits.primitiveWorkBound bits)
  · intro code
    exact (hleaf code).trans (Nat.le_add_right _ _)
  · intro first second hf hs
    exact (RationalBits.add_work first second bits hf hs).trans (Nat.le_add_left _ _)
  · intro first second hf hs
    exact (RationalBits.multiply_work first second bits hf hs).trans (Nat.le_add_left _ _)
  · intro input _
    exact (RationalBits.negate_work input bits).trans (Nat.le_add_left _ _)
  · intro input _
    exact (RationalBits.inverse_work input bits).trans (Nat.le_add_left _ _)
  · exact hvalues

end StoredScalarProgram

/-- A fixed finite rational syntax admits finite preencoded binary literals.
This constructs the program before execution, rather than putting a rational
encoding oracle inside the evaluator. Dynamic values use the leaf API. -/
theorem ScalarProgram.exists_binaryStored {Scalar : Type*} (program : ScalarProgram Scalar) :
    ∃ stored : StoredScalarProgram Scalar RationalBits,stored.meaning RationalBits.decode=program := by
  induction program with
  | rational q =>
    obtain ⟨code,hcode⟩ := RationalBits.exists_code q
    exact ⟨.literal code,congrArg ScalarProgram.rational hcode⟩
  | atom code => exact ⟨.atom code,rfl⟩
  | add first second hf hs =>
    obtain ⟨f,hf⟩ := hf
    obtain ⟨s,hs⟩ := hs
    exact ⟨.add f s,by simp only [StoredScalarProgram.meaning,hf,hs]⟩
  | multiply first second hf hs =>
    obtain ⟨f,hf⟩ := hf
    obtain ⟨s,hs⟩ := hs
    exact ⟨.multiply f s,by simp only [StoredScalarProgram.meaning,hf,hs]⟩
  | negate term ih =>
    obtain ⟨t,ht⟩ := ih
    exact ⟨.negate t,by simp only [StoredScalarProgram.meaning,ht]⟩
  | inverse term ih =>
    obtain ⟨t,ht⟩ := ih
    exact ⟨.inverse t,by simp only [StoredScalarProgram.meaning,ht]⟩

end AFT.RationalNumerics

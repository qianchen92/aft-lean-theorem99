import AFT.CountedScalarCompilation

/-! Literal magnitude and scalar-leaf heights discharge all intermediate
operand obligations in the counted binary scalar compiler and evaluator. -/
namespace AFT.RationalNumerics
open RationalRejectionProgram BinaryArithmetic Polynomial

theorem RationalLiteralBound.literalHeight {value : ℚ} {bound : ℕ}
    (h : RationalLiteralBound value bound) : rationalLiteralHeight value≤2*bound := by
  have hn : value.num.natAbs.size≤bound :=
    Nat.size_le.mpr (h.1.trans_lt (Nat.lt_two_pow_self (n:=bound)))
  have hd : value.den.size≤bound :=
    Nat.size_le.mpr (h.2.trans_lt (Nat.lt_two_pow_self (n:=bound)))
  unfold rationalLiteralHeight
  omega

namespace ScalarProgram
variable {Scalar : Type*}

theorem LiteralBound.literalsBounded {program : ScalarProgram Scalar} {bound : ℕ}
    (h : program.LiteralBound bound) : program.literalsBounded (2*bound) := by
  induction program with
  | rational value => exact RationalLiteralBound.literalHeight h
  | atom code => trivial
  | add first second hf hs | multiply first second hf hs => exact ⟨hf h.1,hs h.2⟩
  | negate term ih | inverse term ih => exact ih h

theorem literalsBounded_mono {program : ScalarProgram Scalar} {first second : ℕ}
    (h : program.literalsBounded first) (hle : first≤second) : program.literalsBounded second := by
  induction program with
  | rational value => exact h.trans hle
  | atom code => trivial
  | add first second hf hs | multiply first second hf hs => exact ⟨hf h.1,hs h.2⟩
  | negate term ih | inverse term ih => exact ih h

theorem bounded_evaluationValues_height (leaf : Scalar → ℚ) (program : ScalarProgram Scalar)
    (literalBound leafBits : ℕ) (hliteral : program.LiteralBound literalBound)
    (hleaf : ∀ code,HeightBound (leaf code) leafBits)
    (value : ℚ) (hvalue : value∈program.evaluationValues leaf) :
    HeightBound value (program.nodes*(leafBits+2*literalBound+1)) := by
  have hh := program.evaluationValues_height leaf (fun _=>leafBits) hleaf value hvalue
  apply hh.mono
  exact program.heightBudget_le (fun _=>leafBits) (leafBits+2*literalBound)
    (fun _=>Nat.le_add_right _ _) (literalsBounded_mono hliteral.literalsBounded (Nat.le_add_left _ _))

theorem compileBinaryRun_work_of_bounds (leaf : Scalar → CountedValue RationalBits)
    (program : ScalarProgram Scalar) (literalBound leafBits leafWork : ℕ)
    (hliteral : program.LiteralBound literalBound)
    (hwork : ∀ code,(leaf code).work≤leafWork)
    (hheight : ∀ code,HeightBound (leaf code).value.decode leafBits) :
    (program.compileBinaryRun leaf).work≤program.nodes*
      (RationalBits.smallRationalEncodingWork literalBound+leafWork+
        RationalBits.primitiveWorkBound (program.nodes*(leafBits+2*literalBound+1))+2)+1 :=
  program.compileBinaryRun_work leaf literalBound _ leafWork hliteral hwork
    (program.bounded_evaluationValues_height _ literalBound leafBits hliteral hheight)

noncomputable def compilationWorkPolynomial (nodeBound literalBound leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  nodeBound*(RationalBits.smallRationalEncodingPolynomial literalBound+leafWork+
    10000000*(nodeBound*(leafBits+2*literalBound+1)+2)^3+2)+1

theorem compileBinaryRun_polynomial_work (leaf : Scalar → CountedValue RationalBits)
    (program : ScalarProgram Scalar) (n : ℕ)
    (nodeBound literalBound leafBits leafWork : Polynomial ℕ)
    (hnodes : program.nodes≤nodeBound.eval n)
    (hliteral : program.LiteralBound (literalBound.eval n))
    (hwork : ∀ code,(leaf code).work≤leafWork.eval n)
    (hheight : ∀ code,HeightBound (leaf code).value.decode (leafBits.eval n)) :
    (program.compileBinaryRun leaf).work≤
      (compilationWorkPolynomial nodeBound literalBound leafBits leafWork).eval n := by
  have hw := program.compileBinaryRun_work_of_bounds leaf _ _ _ hliteral hwork hheight
  have hh := RationalBits.primitiveWorkBound_mono
    (Nat.mul_le_mul_right (leafBits.eval n+2*literalBound.eval n+1) hnodes)
  have hb := Nat.mul_le_mul hnodes
    (Nat.add_le_add_right (Nat.add_le_add_left hh
      (RationalBits.smallRationalEncodingWork (literalBound.eval n)+leafWork.eval n)) 2)
  apply hw.trans
  apply (Nat.add_le_add_right hb 1).trans_eq
  simp only [compilationWorkPolynomial,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,
    RationalBits.smallRationalEncodingPolynomial_eval,RationalBits.primitiveWorkBound]

end ScalarProgram
end AFT.RationalNumerics

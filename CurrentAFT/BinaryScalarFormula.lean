import CurrentAFT.BinaryMassLiftFormula

/-! # Executed fixed scalar syntax with every stored operand copied -/
namespace CurrentAFT.BinaryScalarFormula
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable {Leaf : Type*}

def read (values : Leaf → RationalBits) (leaf : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values leaf)
  ⟨result.data,result.work+1⟩

def current (program : ScalarProgram Leaf) (values : Leaf → RationalBits) : RationalResult :=
  let result := program.compileBinaryRun (read values)
  ⟨result.value,result.work+1⟩

theorem current_value (program : ScalarProgram Leaf) (values : Leaf → RationalBits) :
    (current program values).data.decode=program.run (fun leaf => (values leaf).decode) := by
  simp only [current,ScalarProgram.compileBinaryRun_value,read,RationalBits.copy_value]

def height (program : ScalarProgram Leaf) (bits : ℕ) := program.nodes*(bits+3)
def work (program : ScalarProgram Leaf) (bits : ℕ) :=
  program.nodes*(smallRationalEncodingWork 1+(4*bits+9)+primitiveWorkBound (height program bits)+2)+2

theorem current_bounds (program : ScalarProgram Leaf) (hliterals : program.LiteralBound 1)
    (values : Leaf → RationalBits) (bits : ℕ) (hh : ∀ leaf, HeightBound (values leaf).decode bits) :
    HeightBound (current program values).data.decode (height program bits) ∧
      (current program values).work ≤ work program bits := by
  have hr (leaf : Leaf) : HeightBound (read values leaf).value.decode bits := by rw [read,RationalBits.copy_value]; exact hh leaf
  have hw (leaf : Leaf) : (read values leaf).work ≤ 4*bits+9 := by
    have h := RationalBits.copy_work (values leaf) bits (hh leaf)
    change _+1 ≤ _; omega
  have w := program.compileBinaryRun_work_of_bounds _ 1 bits (4*bits+9) hliterals hw hr
  have h := program.run_height (fun leaf => (read values leaf).value.decode) (fun _ => bits) hr
  have hb := program.heightBudget_le (fun _ => bits) (bits+2) (fun _ => Nat.le_add_right _ _)
    (ScalarProgram.literalsBounded_mono hliterals.literalsBounded (Nat.le_add_left _ _))
  constructor
  · change HeightBound (program.compileBinaryRun (read values)).value.decode _
    rw [ScalarProgram.compileBinaryRun_value]
    exact h.mono (hb.trans_eq (by unfold height; congr 1))
  · change (program.compileBinaryRun (read values)).work+1 ≤ _
    unfold work height
    simp only [Nat.mul_one,Nat.add_assoc,Nat.reduceAdd] at w ⊢
    omega

noncomputable def heightPolynomial (program : ScalarProgram Leaf) (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C program.nodes*(bits+3)
noncomputable def workPolynomial (program : ScalarProgram Leaf) (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C program.nodes*(smallRationalEncodingPolynomial 1+(4*bits+9)+primitiveWorkPolynomial (heightPolynomial program bits)+2)+2

theorem heightPolynomial_eval (program : ScalarProgram Leaf) (bits : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial program bits).eval security=height program (bits.eval security) := by
  simp only [heightPolynomial,height,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_ofNat]
theorem workPolynomial_eval (program : ScalarProgram Leaf) (bits : Polynomial ℕ) (security : ℕ) :
    (workPolynomial program bits).eval security=work program (bits.eval security) := by
  simp only [workPolynomial,work,heightPolynomial_eval,smallRationalEncodingPolynomial_eval,primitiveWorkPolynomial_eval,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]

end CurrentAFT.BinaryScalarFormula

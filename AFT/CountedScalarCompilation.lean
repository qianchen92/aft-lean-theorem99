import AFT.SmallRationalEncoding
import AFT.BinaryStoredScalar

/-! # Counted compilation and execution of stored scalar programs

Compilation traverses the given scalar syntax and encodes every literal.
The input syntax and its rational records must already have been generated;
their generation costs are separate from the proved compilation cost.
-/
namespace AFT.RationalNumerics
open RationalRejectionProgram BinaryArithmetic

namespace StoredScalarProgram
variable {Scalar Value : Type*}

def compileCounted (encode : ℚ → CountedValue Value) :
    ScalarProgram Scalar → CountedValue (StoredScalarProgram Scalar Value)
  | .rational value =>
      let result := encode value
      ⟨.literal result.value,result.work+1⟩
  | .atom code => ⟨.atom code,1⟩
  | .add first second =>
      let left := compileCounted encode first
      let right := compileCounted encode second
      ⟨.add left.value right.value,left.work+right.work+1⟩
  | .multiply first second =>
      let left := compileCounted encode first
      let right := compileCounted encode second
      ⟨.multiply left.value right.value,left.work+right.work+1⟩
  | .negate term =>
      let input := compileCounted encode term
      ⟨.negate input.value,input.work+1⟩
  | .inverse term =>
      let input := compileCounted encode term
      ⟨.inverse input.value,input.work+1⟩

theorem compileCounted_value (encode : ℚ → CountedValue Value) (program : ScalarProgram Scalar) :
    (compileCounted encode program).value=compile (fun value =>(encode value).value) program := by
  induction program <;> simp_all only [compileCounted,compile]

theorem compileCounted_meaning (encode : ℚ → CountedValue Value) (decode : Value → ℚ)
    (hcode : ∀ value,decode (encode value).value=value) (program : ScalarProgram Scalar) :
    (compileCounted encode program).value.meaning decode=program := by
  rw [compileCounted_value]
  exact compile_meaning _ _ hcode program

theorem compileCounted_work (encode : ℚ → CountedValue Value) (bound budget : ℕ)
    (hencode : ∀ value,RationalLiteralBound value bound → (encode value).work≤budget)
    (program : ScalarProgram Scalar) (hprogram : program.LiteralBound bound) :
    (compileCounted encode program).work≤program.nodes*(budget+1) := by
  induction program with
  | rational value => simpa only [compileCounted,ScalarProgram.nodes,one_mul] using Nat.add_le_add_right (hencode value hprogram) 1
  | atom code => simp only [compileCounted,ScalarProgram.nodes,one_mul];omega
  | add first second hf hs | multiply first second hf hs =>
    have hfirst := hf hprogram.1
    have hsecond := hs hprogram.2
    simp only [compileCounted,ScalarProgram.nodes]
    nlinarith
  | negate term ih | inverse term ih =>
    have ht := ih hprogram
    simp only [compileCounted,ScalarProgram.nodes]
    nlinarith

end StoredScalarProgram

namespace ScalarProgram
variable {Scalar : Type*}

def binaryCompile (program : ScalarProgram Scalar) : CountedValue (StoredScalarProgram Scalar RationalBits) :=
  StoredScalarProgram.compileCounted (fun value =>
    let result := RationalBits.encodeSmallRational value
    ⟨result.data,result.work⟩) program

theorem binaryCompile_meaning (program : ScalarProgram Scalar) :
    (program.binaryCompile).value.meaning RationalBits.decode=program :=
  StoredScalarProgram.compileCounted_meaning _ _ RationalBits.encodeSmallRational_value program

theorem binaryCompile_work (program : ScalarProgram Scalar) (bound : ℕ)
    (hprogram : program.LiteralBound bound) :
    program.binaryCompile.work≤program.nodes*(RationalBits.smallRationalEncodingWork bound+1) :=
  StoredScalarProgram.compileCounted_work _ bound _
    (fun value hvalue =>RationalBits.encodeSmallRational_work value bound hvalue) program hprogram

/-- Both runtime literal compilation and numeric evaluation are included.
No decoding or existential choice is executed by this function. -/
def compileBinaryRun (leaf : Scalar → CountedValue RationalBits) (program : ScalarProgram Scalar) :
    CountedValue RationalBits :=
  let compiled := program.binaryCompile
  let result := compiled.value.binaryRun leaf
  ⟨result.value,compiled.work+result.work+1⟩

theorem compileBinaryRun_value (leaf : Scalar → CountedValue RationalBits) (program : ScalarProgram Scalar) :
    (program.compileBinaryRun leaf).value.decode=program.run (fun code =>(leaf code).value.decode) := by
  simp only [compileBinaryRun,StoredScalarProgram.binaryRun_value,binaryCompile_meaning]

theorem compileBinaryRun_work (leaf : Scalar → CountedValue RationalBits) (program : ScalarProgram Scalar)
    (literalBound bits leafWork : ℕ) (hliteral : program.LiteralBound literalBound)
    (hleaf : ∀ code,(leaf code).work≤leafWork)
    (hvalues : ∀ value∈program.evaluationValues (fun code =>(leaf code).value.decode),HeightBound value bits) :
    (program.compileBinaryRun leaf).work≤program.nodes*
      (RationalBits.smallRationalEncodingWork literalBound+leafWork+RationalBits.primitiveWorkBound bits+2)+1 := by
  have hc := program.binaryCompile_work literalBound hliteral
  have hr := (program.binaryCompile).value.binaryRun_work leaf bits leafWork hleaf
    (by simpa only [binaryCompile_meaning] using hvalues)
  rw [binaryCompile_meaning] at hr
  simp only [compileBinaryRun]
  nlinarith

end ScalarProgram
end AFT.RationalNumerics

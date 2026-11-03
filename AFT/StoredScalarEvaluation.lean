import AFT.ScalarOperationalEvaluation

/-! # Scalar evaluation with stored encoded literals

All literals in executable syntax are already numeric representations.
There is no run-time rational-to-binary oracle: compiling the fixed scalar
syntax is separate from evaluating it. Dynamic integers can instead be
supplied by an explicit integer program through the leaf interface.
-/
namespace AFT.RationalNumerics
open RationalRejectionProgram

structure RationalOperations (Value : Type*) where
  add : Value → Value → CountedValue Value
  multiply : Value → Value → CountedValue Value
  negate : Value → CountedValue Value
  inverse : Value → CountedValue Value

structure RationalOperations.Correct {Value : Type*}
    (ops : RationalOperations Value) (decode : Value → ℚ) : Prop where
  add : ∀ first second,decode (ops.add first second).value=decode first+decode second
  multiply : ∀ first second,decode (ops.multiply first second).value=decode first*decode second
  negate : ∀ value,decode (ops.negate value).value=-(decode value)
  inverse : ∀ value,decode (ops.inverse value).value=(decode value)⁻¹

inductive StoredScalarProgram (Scalar Value : Type*) where
  | literal : Value → StoredScalarProgram Scalar Value
  | atom : Scalar → StoredScalarProgram Scalar Value
  | add : StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value
  | multiply : StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value
  | negate : StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value
  | inverse : StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value

namespace StoredScalarProgram
variable {Scalar Value : Type*}

/-- Read-only stored literals need one syntax dispatch. Numeric operations
are charged by their actual implementations. -/
def run (ops : RationalOperations Value) (leaf : Scalar → CountedValue Value) :
    StoredScalarProgram Scalar Value → CountedValue Value
  | .literal value => ⟨value,1⟩
  | .atom code => let result := leaf code;⟨result.value,result.work+1⟩
  | .add first second =>
      let left := first.run ops leaf
      let right := second.run ops leaf
      let result := ops.add left.value right.value
      ⟨result.value,left.work+right.work+result.work+1⟩
  | .multiply first second =>
      let left := first.run ops leaf
      let right := second.run ops leaf
      let result := ops.multiply left.value right.value
      ⟨result.value,left.work+right.work+result.work+1⟩
  | .negate term =>
      let input := term.run ops leaf
      let result := ops.negate input.value
      ⟨result.value,input.work+result.work+1⟩
  | .inverse term =>
      let input := term.run ops leaf
      let result := ops.inverse input.value
      ⟨result.value,input.work+result.work+1⟩

/-- Erasure into rational semantics is used only by proofs. -/
def meaning (decode : Value → ℚ) : StoredScalarProgram Scalar Value → ScalarProgram Scalar
  | .literal value => .rational (decode value)
  | .atom code => .atom code
  | .add first second => .add (first.meaning decode) (second.meaning decode)
  | .multiply first second => .multiply (first.meaning decode) (second.meaning decode)
  | .negate term => .negate (term.meaning decode)
  | .inverse term => .inverse (term.meaning decode)

theorem run_value (ops : RationalOperations Value) (decode : Value → ℚ)
    (hops : ops.Correct decode) (leaf : Scalar → CountedValue Value)
    (program : StoredScalarProgram Scalar Value) :
    decode (program.run ops leaf).value=(program.meaning decode).run (fun code => decode (leaf code).value) := by
  induction program <;> simp_all only [run,meaning,ScalarProgram.run,hops.add,hops.multiply,hops.negate,hops.inverse]

/-- This theorem charges the numeric calls on all actual intermediate
operands. It needs no cost or correctness assumption for a literal encoder. -/
theorem run_work (ops : RationalOperations Value) (decode : Value → ℚ)
    (hops : ops.Correct decode) (leaf : Scalar → CountedValue Value) (bits budget : ℕ)
    (hleaf : ∀ code,(leaf code).work≤ budget)
    (hadd : ∀ first second,HeightBound (decode first) bits → HeightBound (decode second) bits →
      (ops.add first second).work≤ budget)
    (hmul : ∀ first second,HeightBound (decode first) bits → HeightBound (decode second) bits →
      (ops.multiply first second).work≤ budget)
    (hneg : ∀ value,HeightBound (decode value) bits → (ops.negate value).work≤ budget)
    (hinv : ∀ value,HeightBound (decode value) bits → (ops.inverse value).work≤ budget)
    (program : StoredScalarProgram Scalar Value)
    (hvalues : ∀ value∈(program.meaning decode).evaluationValues (fun code => decode (leaf code).value),
      HeightBound value bits) :
    (program.run ops leaf).work≤ (program.meaning decode).nodes*(budget+1) := by
  induction program with
  | literal value => simp only [run,meaning,ScalarProgram.nodes,one_mul];omega
  | atom code =>
      have hh := hleaf code
      simp only [run,meaning,ScalarProgram.nodes,one_mul]
      omega
  | add first second hf hs =>
      have hvf : ∀ value∈(first.meaning decode).evaluationValues (fun code => decode (leaf code).value),
          HeightBound value bits :=
        fun value hv => hvalues value (by
          simp only [meaning,ScalarProgram.evaluationValues,List.mem_append];exact Or.inl (Or.inl hv))
      have hvs : ∀ value∈(second.meaning decode).evaluationValues (fun code => decode (leaf code).value),
          HeightBound value bits :=
        fun value hv => hvalues value (by
          simp only [meaning,ScalarProgram.evaluationValues,List.mem_append];exact Or.inl (Or.inr hv))
      have ho := hadd (first.run ops leaf).value (second.run ops leaf).value
        (by rw [run_value ops decode hops];exact hvf _ (ScalarProgram.run_mem_evaluationValues _ _))
        (by rw [run_value ops decode hops];exact hvs _ (ScalarProgram.run_mem_evaluationValues _ _))
      have hwf := hf hvf
      have hws := hs hvs
      simp only [run,meaning,ScalarProgram.nodes]
      nlinarith
  | multiply first second hf hs =>
      have hvf : ∀ value∈(first.meaning decode).evaluationValues (fun code => decode (leaf code).value),
          HeightBound value bits :=
        fun value hv => hvalues value (by
          simp only [meaning,ScalarProgram.evaluationValues,List.mem_append];exact Or.inl (Or.inl hv))
      have hvs : ∀ value∈(second.meaning decode).evaluationValues (fun code => decode (leaf code).value),
          HeightBound value bits :=
        fun value hv => hvalues value (by
          simp only [meaning,ScalarProgram.evaluationValues,List.mem_append];exact Or.inl (Or.inr hv))
      have ho := hmul (first.run ops leaf).value (second.run ops leaf).value
        (by rw [run_value ops decode hops];exact hvf _ (ScalarProgram.run_mem_evaluationValues _ _))
        (by rw [run_value ops decode hops];exact hvs _ (ScalarProgram.run_mem_evaluationValues _ _))
      have hwf := hf hvf
      have hws := hs hvs
      simp only [run,meaning,ScalarProgram.nodes]
      nlinarith
  | negate term ih =>
      have hvt : ∀ value∈(term.meaning decode).evaluationValues (fun code => decode (leaf code).value),
          HeightBound value bits :=
        fun value hv => hvalues value (List.mem_append_left _ hv)
      have ho := hneg (term.run ops leaf).value
        (by rw [run_value ops decode hops];exact hvt _ (ScalarProgram.run_mem_evaluationValues _ _))
      have hwt := ih hvt
      simp only [run,meaning,ScalarProgram.nodes]
      nlinarith
  | inverse term ih =>
      have hvt : ∀ value∈(term.meaning decode).evaluationValues (fun code => decode (leaf code).value),
          HeightBound value bits :=
        fun value hv => hvalues value (List.mem_append_left _ hv)
      have ho := hinv (term.run ops leaf).value
        (by rw [run_value ops decode hops];exact hvt _ (ScalarProgram.run_mem_evaluationValues _ _))
      have hwt := ih hvt
      simp only [run,meaning,ScalarProgram.nodes]
      nlinarith

/-- Compilation is outside the execution loop. An application must supply
stored codes for its literals, or generate dynamic values through `leaf`. -/
def compile (encode : ℚ → Value) : ScalarProgram Scalar → StoredScalarProgram Scalar Value
  | .rational value => .literal (encode value)
  | .atom code => .atom code
  | .add first second => .add (compile encode first) (compile encode second)
  | .multiply first second => .multiply (compile encode first) (compile encode second)
  | .negate term => .negate (compile encode term)
  | .inverse term => .inverse (compile encode term)

theorem compile_meaning (encode : ℚ → Value) (decode : Value → ℚ)
    (hcode : ∀ value,decode (encode value)=value) (program : ScalarProgram Scalar) :
    (compile encode program).meaning decode=program := by
  induction program <;> simp_all only [compile,meaning]

end StoredScalarProgram
end AFT.RationalNumerics

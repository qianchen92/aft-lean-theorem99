import AFT.ScalarProgramResources
import AFT.CountedRationalRejection

/-! # Executing scalar syntax in an explicit numeric representation

The evaluator calls the supplied numeric programs on the actual stored
child results. It never decodes to rationals during execution. Correctness
and bounded operand costs are separate proved interfaces for instantiation
by the binary numerator/denominator implementation.
-/
namespace AFT.RationalNumerics
open RationalRejectionProgram

structure RationalImplementation (Value : Type*) where
  literal : ℚ → CountedValue Value
  add : Value → Value → CountedValue Value
  multiply : Value → Value → CountedValue Value
  negate : Value → CountedValue Value
  inverse : Value → CountedValue Value

structure RationalImplementation.Correct {Value : Type*}
    (ops : RationalImplementation Value) (decode : Value → ℚ) : Prop where
  literal : ∀ value,decode (ops.literal value).value=value
  add : ∀ first second,decode (ops.add first second).value=decode first+decode second
  multiply : ∀ first second,decode (ops.multiply first second).value=decode first*decode second
  negate : ∀ value,decode (ops.negate value).value=-(decode value)
  inverse : ∀ value,decode (ops.inverse value).value=(decode value)⁻¹

namespace ScalarProgram
variable {Scalar Value : Type*}

/-- Every recursive child and primitive result is evaluated once. The extra
unit per node charges the syntax dispatch and result storage. -/
def runWith (ops : RationalImplementation Value) (leaf : Scalar → CountedValue Value) :
    ScalarProgram Scalar → CountedValue Value
  | .rational value => let result := ops.literal value;⟨result.value,result.work+1⟩
  | .atom code => let result := leaf code;⟨result.value,result.work+1⟩
  | .add first second =>
      let left := first.runWith ops leaf
      let right := second.runWith ops leaf
      let result := ops.add left.value right.value
      ⟨result.value,left.work+right.work+result.work+1⟩
  | .multiply first second =>
      let left := first.runWith ops leaf
      let right := second.runWith ops leaf
      let result := ops.multiply left.value right.value
      ⟨result.value,left.work+right.work+result.work+1⟩
  | .negate term =>
      let input := term.runWith ops leaf
      let result := ops.negate input.value
      ⟨result.value,input.work+result.work+1⟩
  | .inverse term =>
      let input := term.runWith ops leaf
      let result := ops.inverse input.value
      ⟨result.value,input.work+result.work+1⟩

theorem runWith_value (ops : RationalImplementation Value) (decode : Value → ℚ)
    (hops : ops.Correct decode) (leaf : Scalar → CountedValue Value) (program : ScalarProgram Scalar) :
    decode (program.runWith ops leaf).value=program.run (fun code => decode (leaf code).value) := by
  induction program <;> simp_all only [runWith,run,hops.literal,hops.add,hops.multiply,hops.negate,hops.inverse]

theorem run_mem_evaluationValues (leaf : Scalar → ℚ) (program : ScalarProgram Scalar) :
    program.run leaf∈program.evaluationValues leaf := by
  cases program <;> simp only [run,evaluationValues,List.mem_append,List.mem_singleton,
    or_true]

/-- A bound for the actual numeric calls, valid only on operands whose
semantic heights are controlled. Instantiating this with binary primitives
turns the existing intermediate-height theorem into a scalar bit-step bound. -/
theorem runWith_work (ops : RationalImplementation Value) (decode : Value → ℚ)
    (hops : ops.Correct decode) (leaf : Scalar → CountedValue Value) (bits budget : ℕ)
    (hliteral : ∀ value,HeightBound value bits → (ops.literal value).work≤ budget)
    (hleaf : ∀ code,(leaf code).work≤ budget)
    (hadd : ∀ first second,HeightBound (decode first) bits → HeightBound (decode second) bits →
      (ops.add first second).work≤ budget)
    (hmul : ∀ first second,HeightBound (decode first) bits → HeightBound (decode second) bits →
      (ops.multiply first second).work≤ budget)
    (hneg : ∀ value,HeightBound (decode value) bits → (ops.negate value).work≤ budget)
    (hinv : ∀ value,HeightBound (decode value) bits → (ops.inverse value).work≤ budget)
    (program : ScalarProgram Scalar)
    (hvalues : ∀ value∈program.evaluationValues (fun code => decode (leaf code).value),HeightBound value bits) :
    (program.runWith ops leaf).work≤ program.nodes*(budget+1) := by
  induction program with
  | rational value =>
      have hh := hliteral value (hvalues value (by simp [evaluationValues]))
      simp only [runWith,nodes,one_mul]
      omega
  | atom code =>
      have hh := hleaf code
      simp only [runWith,nodes,one_mul]
      omega
  | add first second hf hs =>
      have hvf : ∀ value∈first.evaluationValues (fun code => decode (leaf code).value),HeightBound value bits :=
        fun value hv => hvalues value (by simp only [evaluationValues,List.mem_append];exact Or.inl (Or.inl hv))
      have hvs : ∀ value∈second.evaluationValues (fun code => decode (leaf code).value),HeightBound value bits :=
        fun value hv => hvalues value (by simp only [evaluationValues,List.mem_append];exact Or.inl (Or.inr hv))
      have ho := hadd (first.runWith ops leaf).value (second.runWith ops leaf).value
        (by rw [runWith_value ops decode hops];exact hvf _ (run_mem_evaluationValues _ _))
        (by rw [runWith_value ops decode hops];exact hvs _ (run_mem_evaluationValues _ _))
      have hwf := hf hvf
      have hws := hs hvs
      simp only [runWith,nodes]
      nlinarith
  | multiply first second hf hs =>
      have hvf : ∀ value∈first.evaluationValues (fun code => decode (leaf code).value),HeightBound value bits :=
        fun value hv => hvalues value (by simp only [evaluationValues,List.mem_append];exact Or.inl (Or.inl hv))
      have hvs : ∀ value∈second.evaluationValues (fun code => decode (leaf code).value),HeightBound value bits :=
        fun value hv => hvalues value (by simp only [evaluationValues,List.mem_append];exact Or.inl (Or.inr hv))
      have ho := hmul (first.runWith ops leaf).value (second.runWith ops leaf).value
        (by rw [runWith_value ops decode hops];exact hvf _ (run_mem_evaluationValues _ _))
        (by rw [runWith_value ops decode hops];exact hvs _ (run_mem_evaluationValues _ _))
      have hwf := hf hvf
      have hws := hs hvs
      simp only [runWith,nodes]
      nlinarith
  | negate term ih =>
      have hvt : ∀ value∈term.evaluationValues (fun code => decode (leaf code).value),HeightBound value bits :=
        fun value hv => hvalues value (List.mem_append_left _ hv)
      have ho := hneg (term.runWith ops leaf).value
        (by rw [runWith_value ops decode hops];exact hvt _ (run_mem_evaluationValues _ _))
      have hwt := ih hvt
      simp only [runWith,nodes]
      nlinarith
  | inverse term ih =>
      have hvt : ∀ value∈term.evaluationValues (fun code => decode (leaf code).value),HeightBound value bits :=
        fun value hv => hvalues value (List.mem_append_left _ hv)
      have ho := hinv (term.runWith ops leaf).value
        (by rw [runWith_value ops decode hops];exact hvt _ (run_mem_evaluationValues _ _))
      have hwt := ih hvt
      simp only [runWith,nodes]
      nlinarith

end ScalarProgram
end AFT.RationalNumerics

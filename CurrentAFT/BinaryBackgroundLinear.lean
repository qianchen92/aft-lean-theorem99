import CurrentAFT.BinaryBackgroundLeaves
import CurrentAFT.BinaryCoefficientScalarAverage
import CurrentAFT.BinaryFamilyValidSemantics
import CurrentAFT.BinaryScalarFormula
import CurrentAFT.BinaryProposalMetadata

/-! # The actual balanced leg-linear certificate, with scalar averaging last -/
namespace CurrentAFT.BinaryBackgroundLinear
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | colors | legs | population | free | mean
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  .multiply (.negate (.add
    (.multiply (.add (.add (.atom .population) (.negate (.atom .legs))) (.negate (.atom .colors))) (.atom .free))
    (.multiply (.atom .colors) (.atom .mean)))) (.inverse (.atom .legs))

theorem expression_literals : expression.LiteralBound 1 := by trivial

def values (metadata : BinaryProposalMetadata.Encoded) (free mean : RationalBits) : Leaf → RationalBits
  | .colors => metadata.colors | .legs => metadata.legs | .population => metadata.population | .free => free | .mean => mean

def meanTranslation (security bits order : ℕ) : CoefficientProgram order :=
  BinaryCoefficientScalarAverage.current security bits order (fun scalar => BinaryBackgroundLeaves.current .translation security bits order scalar)

def current (security bits order : ℕ) : CoefficientProgram order :=
  fun arity inputs centers =>
    let metadata := BinaryProposalMetadata.current security
    let free := BinaryBackgroundLeaves.current .free security bits order IntegerBits.zero arity inputs centers
    let mean := meanTranslation security bits order arity inputs centers
    let result := BinaryScalarFormula.current expression (values metadata free.value mean.value)
    ⟨result.data,metadata.work+free.work+mean.work+result.work+4⟩

noncomputable section
theorem meanTranslation_value (security bits order : ℕ) (arity : TruncatedArity order)
    (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (meanTranslation security bits order arity inputs centers).value.decode=
      RationalBackgroundLinearProgram.meanTranslation security bits order arity inputs.get centers.get := by
  exact BinaryFamilyValidSemantics.scalarAverage_value security bits order (BinaryFirstInverseProgram.colors security) _ _
    (fun scalar => BinaryBackgroundLeaves.current_value .translation security bits order scalar) arity inputs centers hi hb

theorem current_value (security bits order : ℕ) (arity : TruncatedArity order)
    (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current security bits order arity inputs centers).value.decode=
      RationalBackgroundLinearProgram.legLinear security bits order arity inputs.get centers.get := by
  rcases BinaryProposalMetadata.current_value security with ⟨hq,hl,hp⟩
  simp only [current,BinaryScalarFormula.current_value,expression,values,ScalarProgram.run,
    BinaryBackgroundLeaves.current_value .free security bits order IntegerBits.zero arity inputs centers hi hb,
    meanTranslation_value security bits order arity inputs centers hi hb,hq,hl,hp,BinaryBackgroundLeaves.ideal,
    RationalBackgroundLinearProgram.legLinear,RationalBackgroundLinearProgram.freeMass,PublicParameterProgram.modulus_value,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,sub_eq_add_neg,div_eq_mul_inv]

noncomputable def scalarBitsPolynomial : Polynomial ℕ := BinaryCoefficientScalarAverage.scalarBitsPolynomial
noncomputable def translationHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryBackgroundLeaves.heightPolynomial .translation precision scalarBitsPolynomial
noncomputable def translationWorkPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ := BinaryBackgroundLeaves.workPolynomial .translation order precision scalarBitsPolynomial
noncomputable def meanHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryCoefficientScalarAverage.heightPolynomial precision (translationHeightPolynomial precision)
noncomputable def meanWorkPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.workPolynomial precision (translationHeightPolynomial precision) (translationWorkPolynomial order precision)
noncomputable def operandPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.sizePolynomial+BinaryBackgroundLeaves.heightPolynomial .free precision scalarBitsPolynomial+meanHeightPolynomial precision
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryScalarFormula.heightPolynomial expression (operandPolynomial precision)
noncomputable def workPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.currentWorkPolynomial+BinaryBackgroundLeaves.workPolynomial .free order precision scalarBitsPolynomial+
    meanWorkPolynomial order precision+BinaryScalarFormula.workPolynomial expression (operandPolynomial precision)+4

theorem meanTranslation_bounds (security order : ℕ) (precision : Polynomial ℕ) (arity : TruncatedArity order)
    (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (meanTranslation security (precision.eval security) order arity inputs centers).value.decode
      ((meanHeightPolynomial precision).eval security) ∧
    (meanTranslation security (precision.eval security) order arity inputs centers).work ≤ (meanWorkPolynomial order precision).eval security :=
  BinaryCoefficientScalarAverage.current_bounds security order (BinaryFirstInverseProgram.colors security) precision _ _ _
    (fun scalar hs => BinaryBackgroundLeaves.current_bounds .translation security order precision scalarBitsPolynomial scalar hs)
    arity inputs centers hi hb

theorem current_bounds (security order : ℕ) (precision : Polynomial ℕ) (arity : TruncatedArity order)
    (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order arity inputs centers).value.decode
      ((heightPolynomial precision).eval security) ∧
    (current security (precision.eval security) order arity inputs centers).work ≤ (workPolynomial order precision).eval security := by
  let metadata := BinaryProposalMetadata.current security
  let free := BinaryBackgroundLeaves.current .free security (precision.eval security) order IntegerBits.zero arity inputs centers
  let mean := meanTranslation security (precision.eval security) order arity inputs centers
  let H := (operandPolynomial precision).eval security
  have hH : H=BinaryProposalMetadata.sizeBound security+(BinaryBackgroundLeaves.heightPolynomial .free precision scalarBitsPolynomial).eval security+
      (meanHeightPolynomial precision).eval security := by simp only [H,operandPolynomial,Polynomial.eval_add,BinaryProposalMetadata.sizePolynomial_eval]
  have hm := BinaryProposalMetadata.current_height security
  have hf := BinaryBackgroundLeaves.current_bounds .free security order precision scalarBitsPolynomial IntegerBits.zero
    (by simp only [IntegerBits.zero,List.length_nil]; exact Nat.zero_le _) arity inputs centers hi hb
  have ha := meanTranslation_bounds security order precision arity inputs centers hi hb
  have h := BinaryScalarFormula.current_bounds expression expression_literals (values metadata free.value mean.value) H (by
    intro leaf
    cases leaf
    · exact hm.1.mono (by rw [hH]; omega)
    · exact hm.2.1.mono (by rw [hH]; omega)
    · exact hm.2.2.mono (by rw [hH]; omega)
    · exact hf.1.mono (by rw [hH]; omega)
    · exact ha.1.mono (by rw [hH]; omega))
  constructor
  · rw [heightPolynomial,BinaryScalarFormula.heightPolynomial_eval]
    exact h.1
  · have wm := BinaryProposalMetadata.current_work security
    change metadata.work+free.work+mean.work+(BinaryScalarFormula.current expression (values metadata free.value mean.value)).work+4 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,BinaryProposalMetadata.currentWorkPolynomial_eval,BinaryScalarFormula.workPolynomial_eval]
    dsimp only [metadata,free,mean,H] at h ⊢
    omega

end
end CurrentAFT.BinaryBackgroundLinear

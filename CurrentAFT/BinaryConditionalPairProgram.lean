import CurrentAFT.BinaryConditionalPairMean
import CurrentAFT.BinaryMassLiftInput
import CurrentAFT.BinaryFirstFamily
import CurrentAFT.BinaryFiniteCoefficient

/-! # The literal current conditional pair mass certificate in binary form -/
namespace CurrentAFT.BinaryConditionalPairProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryMassLiftInput.current BinaryFirstFamily.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def density (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (BinaryConditionalPairMean.current security bits scalar) output

theorem density_value (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) :
    (density security bits scalar output).data.decode=RationalMassLiftProgram.current security bits
      (RationalConditionalPairProgram.centeredMean security bits scalar.decode) output.val :=
  BinaryMassLiftInput.current_value security bits _ _ output (BinaryConditionalPairMean.current_value security bits scalar)

def finite (security bits order : ℕ) (scalar : IntegerBits) : BinaryFiniteCoefficient.FiniteProgram security order :=
  fun arity inputs centers => BinaryFirstFamily.current security arity.val.1.val arity.val.2.val
    (density security bits scalar) (fun _ => ⟨zero,2⟩) inputs centers

theorem finite_value (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) :
    (finite security bits order scalar arity inputs centers).data.decode=RationalConditionalPairProgram.current security bits order scalar.decode arity
      (fun index => (inputs.get index).val) (fun index => (centers.get index).val) :=
  BinaryFirstFamily.current_value security order arity _ _ _ _ inputs centers (density_value security bits scalar) (fun _ => zero_value)

def current (security bits order : ℕ) (scalar : IntegerBits) : BinaryFamilyProduct.CoefficientProgram order :=
  BinaryFiniteCoefficient.lift security order (finite security bits order scalar)

theorem current_value (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<colors security) (hb : ∀ index, centers.get index<colors security) :
    (current security bits order scalar arity inputs centers).value.decode=RationalConditionalPairProgram.current security bits order scalar.decode arity inputs.get centers.get :=
  BinaryFiniteCoefficient.lift_value security order (finite security bits order scalar) _ (finite_value security bits order scalar) arity inputs centers hi hb

noncomputable section
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (BinaryConditionalPairMean.heightPolynomial precision scalarBits)
noncomputable def densityWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (BinaryConditionalPairMean.heightPolynomial precision scalarBits)
    (BinaryConditionalPairMean.workPolynomial precision scalarBits)
noncomputable def finiteWorkPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  densityWorkPolynomial precision scalarBits+Polynomial.C (15*order+52)
noncomputable def workPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteCoefficient.workPolynomial order (finiteWorkPolynomial order precision scalarBits)

theorem density_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (output : Fin (colors security)) :
    HeightBound (density security (precision.eval security) scalar output).data.decode ((heightPolynomial precision scalarBits).eval security) ∧
      (density security (precision.eval security) scalar output).work ≤ (densityWorkPolynomial precision scalarBits).eval security :=
  BinaryMassLiftInput.current_bounds security precision (BinaryConditionalPairMean.heightPolynomial precision scalarBits)
    (BinaryConditionalPairMean.workPolynomial precision scalarBits) (BinaryConditionalPairMean.current security (precision.eval security) scalar) output
    (fun color => (BinaryConditionalPairMean.current_bounds security precision scalarBits scalar hs color).1)
    (fun color => (BinaryConditionalPairMean.current_bounds security precision scalarBits scalar hs color).2)

theorem finite_bounds (security order : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) :
    HeightBound (finite security (precision.eval security) order scalar arity inputs centers).data.decode ((heightPolynomial precision scalarBits).eval security) ∧
      (finite security (precision.eval security) order scalar arity inputs centers).work ≤ (finiteWorkPolynomial order precision scalarBits).eval security := by
  have h := BinaryFirstFamily.current_bounds security arity.val.1.val arity.val.2.val (density security (precision.eval security) scalar)
    (fun _ => ⟨zero,2⟩) inputs centers ((heightPolynomial precision scalarBits).eval security) 0
    ((densityWorkPolynomial precision scalarBits).eval security) 2
    (fun color => (density_bounds security precision scalarBits scalar hs color).1) (fun _ => by rw [zero_value]; exact HeightBound.zero)
    (fun color => (density_bounds security precision scalarBits scalar hs color).2) (fun _ => le_refl _)
  refine ⟨by simpa only [add_zero] using h.1,h.2.trans ?_⟩
  have hd := arity.property
  simp only [BinaryFirstFamily.work,finiteWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
  omega

theorem current_bounds (security order : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (arity : TruncatedArity order)
    (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<colors security) (hb : ∀ index, centers.get index<colors security) :
    HeightBound (current security (precision.eval security) order scalar arity inputs centers).value.decode ((heightPolynomial precision scalarBits).eval security) ∧
      (current security (precision.eval security) order scalar arity inputs centers).work ≤ (workPolynomial order precision scalarBits).eval security :=
  BinaryFiniteCoefficient.lift_bounds security order (heightPolynomial precision scalarBits) (finiteWorkPolynomial order precision scalarBits)
    (finite security (precision.eval security) order scalar)
    (fun arity inputs centers => (finite_bounds security order precision scalarBits scalar hs arity inputs centers).1)
    (fun arity inputs centers => (finite_bounds security order precision scalarBits scalar hs arity inputs centers).2)
    arity inputs centers hi hb

end
end CurrentAFT.BinaryConditionalPairProgram

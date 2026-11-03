import CurrentAFT.FixedFamilyPrograms

/-! # Uniform fixed-order coefficient programs with derived bit bounds -/
namespace CurrentAFT.BinaryFamilyArithmetic
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra RationalFamilyProductProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- `programs` is a single finite constant list for the fixed order. -/
def multiply (order : ℕ) (programs : List (Entry order)) (first second : CoefficientProgram order) :
    CoefficientProgram order := fun arity colors centers =>
  let selected := lookup order arity programs
  let product := BinaryFamilyProduct.run order arity selected.value first second colors centers
  ⟨product.value, selected.work+product.work+1⟩

def multiplyHeight (order : ℕ) (programs : List (Entry order)) (bits : ℕ) : ℕ :=
  nodes programs * (bits + literals programs + 1)

def multiplyWork (order : ℕ) (programs : List (Entry order)) (bits budget : ℕ) : ℕ :=
  programs.length*(12*order+7)+1 + nodes programs *
    (leafWork order budget + primitiveWorkBound (multiplyHeight order programs bits) + 1) + 1

noncomputable section
open scoped Classical

theorem multiply_value (order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (first second : CoefficientProgram order) (firstTable secondTable : Table ℚ ℕ ℕ order)
    (hfirst : ∀ arity colors centers, (first arity colors centers).value.decode = firstTable arity colors.get centers.get)
    (hsecond : ∀ arity colors centers, (second arity colors centers).value.decode = secondTable arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (multiply order programs first second arity colors centers).value.decode =
      product order firstTable secondTable arity colors.get centers.get :=
  BinaryFamilyProduct.run_value order arity (lookup order arity programs).value
    (lookup_meaning order arity programs hcorrect (hcomplete arity))
    first second firstTable secondTable hfirst hsecond colors centers

theorem multiply_bounds (order base bits budget : ℕ) (programs : List (Entry order))
    (first second : CoefficientProgram order)
    (hfirst : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (first arity colors centers).value.decode bits ∧ (first arity colors centers).work ≤ budget)
    (hsecond : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (second arity colors centers).value.decode bits ∧ (second arity colors centers).work ≤ budget)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base) :
    HeightBound (multiply order programs first second arity colors centers).value.decode
        (multiplyHeight order programs bits) ∧
      (multiply order programs first second arity colors centers).work ≤ multiplyWork order programs bits budget := by
  let selected := lookup order arity programs
  have hb := lookup_bounds order arity programs
  have he := BinaryFamilyProduct.run_bounds order base bits budget arity selected.value
    first second hfirst hsecond colors centers hcolors hcenters
  have hh : BinaryFixedScalarProgram.height selected.value bits ≤ multiplyHeight order programs bits := by
    unfold BinaryFixedScalarProgram.height multiplyHeight
    gcongr
    · exact hb.1
    · exact hb.2
  have hw : BinaryFixedScalarProgram.work selected.value bits (leafWork order budget) ≤
      nodes programs * (leafWork order budget + primitiveWorkBound (multiplyHeight order programs bits) + 1) := by
    unfold BinaryFixedScalarProgram.work primitiveWorkBound
    gcongr
    exact hb.1
  refine ⟨he.1.mono hh, ?_⟩
  have hl := lookup_work order arity programs
  have hr := he.2.trans hw
  change selected.work + (BinaryFamilyProduct.run order arity selected.value first second colors centers).work + 1 ≤ _
  unfold multiplyWork
  exact Nat.add_le_add_right (Nat.add_le_add hl hr) 1

noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order))
    (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (nodes programs) * (bits + Polynomial.C (literals programs) + 1)

noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order))
    (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (programs.length*(12*order+7)+1) + Polynomial.C (nodes programs) *
    (Polynomial.C (2*order*(6*order+10)+9) + budget +
      BinaryCalibrationIteration.primitivePolynomial (heightPolynomial order programs bits) + 1) + 1

theorem heightPolynomial_eval (order : ℕ) (programs : List (Entry order))
    (bits : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial order programs bits).eval security = multiplyHeight order programs (bits.eval security) := by
  simp [heightPolynomial, multiplyHeight]

theorem workPolynomial_eval (order : ℕ) (programs : List (Entry order))
    (bits budget : Polynomial ℕ) (security : ℕ) :
    (workPolynomial order programs bits budget).eval security =
      multiplyWork order programs (bits.eval security) (budget.eval security) := by
  simp only [workPolynomial, multiplyWork, BinaryCalibrationIteration.primitivePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_one, heightPolynomial_eval, primitiveWorkBound, leafWork]
  ring

end
end CurrentAFT.BinaryFamilyArithmetic

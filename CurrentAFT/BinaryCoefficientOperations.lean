import CurrentAFT.BinaryFamilyArithmetic
import CurrentAFT.BinaryFamilyValidSemantics

/-! # Executed coefficient sums and compositional polynomial resource bounds -/
namespace CurrentAFT.BinaryCoefficientOperations
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def add (order : ℕ) (first second : CoefficientProgram order) : CoefficientProgram order :=
  fun arity inputs centers =>
    let a := first arity inputs centers
    let b := second arity inputs centers
    let result := RationalBits.add a.value b.value
    ⟨result.data,a.work+b.work+result.work+3⟩

theorem add_value (order : ℕ) (first second : CoefficientProgram order)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (add order first second arity inputs centers).value.decode=
      (first arity inputs centers).value.decode+(second arity inputs centers).value.decode := by
  simp only [add,RationalBits.add_value]

noncomputable section
noncomputable def addHeight (firstBits secondBits : Polynomial ℕ) : Polynomial ℕ := firstBits+secondBits+1
noncomputable def addWork (firstBits secondBits firstWork secondWork : Polynomial ℕ) : Polynomial ℕ :=
  firstWork+secondWork+primitiveWorkPolynomial (firstBits+secondBits)+3

theorem add_bounds (order base security : ℕ) (first second : CoefficientProgram order)
    (firstBits secondBits firstWork secondWork : Polynomial ℕ)
    (hfirst : ∀ arity inputs centers, (∀ i, inputs.get i<base) → (∀ i, centers.get i<base) →
      HeightBound (first arity inputs centers).value.decode (firstBits.eval security) ∧
        (first arity inputs centers).work ≤ firstWork.eval security)
    (hsecond : ∀ arity inputs centers, (∀ i, inputs.get i<base) → (∀ i, centers.get i<base) →
      HeightBound (second arity inputs centers).value.decode (secondBits.eval security) ∧
        (second arity inputs centers).work ≤ secondWork.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<base) (hb : ∀ i, centers.get i<base) :
    HeightBound (add order first second arity inputs centers).value.decode ((addHeight firstBits secondBits).eval security) ∧
      (add order first second arity inputs centers).work ≤ (addWork firstBits secondBits firstWork secondWork).eval security := by
  have hf := hfirst arity inputs centers hi hb
  have hs := hsecond arity inputs centers hi hb
  have wa := RationalBits.add_work (first arity inputs centers).value (second arity inputs centers).value
    ((firstBits+secondBits).eval security) (hf.1.mono (by simp only [Polynomial.eval_add]; omega)) (hs.1.mono (by simp only [Polynomial.eval_add]; omega))
  constructor
  · rw [add_value]
    simpa only [addHeight,Polynomial.eval_add,Polynomial.eval_one] using hf.1.add hs.1
  · change (first arity inputs centers).work+(second arity inputs centers).work+_+3 ≤ _
    simp only [addWork,Polynomial.eval_add,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval] at wa ⊢
    omega

theorem multiply_bounds (order base security : ℕ) (programs : List (Entry order)) (first second : CoefficientProgram order)
    (firstBits secondBits firstWork secondWork : Polynomial ℕ)
    (hfirst : ∀ arity inputs centers, (∀ i, inputs.get i<base) → (∀ i, centers.get i<base) →
      HeightBound (first arity inputs centers).value.decode (firstBits.eval security) ∧
        (first arity inputs centers).work ≤ firstWork.eval security)
    (hsecond : ∀ arity inputs centers, (∀ i, inputs.get i<base) → (∀ i, centers.get i<base) →
      HeightBound (second arity inputs centers).value.decode (secondBits.eval security) ∧
        (second arity inputs centers).work ≤ secondWork.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<base) (hb : ∀ i, centers.get i<base) :
    HeightBound (BinaryFamilyArithmetic.multiply order programs first second arity inputs centers).value.decode
      ((BinaryFamilyArithmetic.heightPolynomial order programs (firstBits+secondBits)).eval security) ∧
    (BinaryFamilyArithmetic.multiply order programs first second arity inputs centers).work ≤
      (BinaryFamilyArithmetic.workPolynomial order programs (firstBits+secondBits) (firstWork+secondWork)).eval security := by
  rw [BinaryFamilyArithmetic.heightPolynomial_eval,BinaryFamilyArithmetic.workPolynomial_eval]
  apply BinaryFamilyArithmetic.multiply_bounds order base _ _ programs first second
    (fun arity inputs centers hi hb => ?_) (fun arity inputs centers hi hb => ?_) arity inputs centers hi hb
  · have h := hfirst arity inputs centers hi hb
    exact ⟨h.1.mono (by simp only [Polynomial.eval_add]; omega),h.2.trans (by simp only [Polynomial.eval_add]; omega)⟩
  · have h := hsecond arity inputs centers hi hb
    exact ⟨h.1.mono (by simp only [Polynomial.eval_add]; omega),h.2.trans (by simp only [Polynomial.eval_add]; omega)⟩

end
end CurrentAFT.BinaryCoefficientOperations

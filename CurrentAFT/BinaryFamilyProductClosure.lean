import CurrentAFT.BinaryFamilyArithmetic

/-! # Composing two verified binary coefficient programs -/
namespace CurrentAFT.BinaryFamilyProductClosure
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1200000
noncomputable section

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (firstBits secondBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs (firstBits+secondBits)
def workPolynomial (order : ℕ) (programs : List (Entry order))
    (firstBits secondBits firstWork secondWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs (firstBits+secondBits) (firstWork+secondWork)

theorem polynomial_bounds (order base security : ℕ) (programs : List (Entry order))
    (first second : CoefficientProgram order) (firstBits secondBits firstWork secondWork : Polynomial ℕ)
    (hfirst : ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      HeightBound (first arity colors centers).value.decode (firstBits.eval security) ∧
        (first arity colors centers).work ≤ firstWork.eval security)
    (hsecond : ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      HeightBound (second arity colors centers).value.decode (secondBits.eval security) ∧
        (second arity colors centers).work ≤ secondWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<base) (hd : ∀ i, centers.get i<base) :
    HeightBound (BinaryFamilyArithmetic.multiply order programs first second arity colors centers).value.decode
      ((heightPolynomial order programs firstBits secondBits).eval security) ∧
      (BinaryFamilyArithmetic.multiply order programs first second arity colors centers).work ≤
        (workPolynomial order programs firstBits secondBits firstWork secondWork).eval security := by
  let H := firstBits+secondBits
  let W := firstWork+secondWork
  have hf (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
      (hc : ∀ i, colors.get i<base) (hd : ∀ i, centers.get i<base) :
      HeightBound (first arity colors centers).value.decode (H.eval security) ∧
        (first arity colors centers).work ≤ W.eval security := by
    have h := hfirst arity colors centers hc hd
    simp only [H,W,Polynomial.eval_add]
    exact ⟨h.1.mono (Nat.le_add_right _ _),h.2.trans (Nat.le_add_right _ _)⟩
  have hs (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
      (hc : ∀ i, colors.get i<base) (hd : ∀ i, centers.get i<base) :
      HeightBound (second arity colors centers).value.decode (H.eval security) ∧
        (second arity colors centers).work ≤ W.eval security := by
    have h := hsecond arity colors centers hc hd
    simp only [H,W,Polynomial.eval_add]
    exact ⟨h.1.mono (Nat.le_add_left _ _),h.2.trans (Nat.le_add_left _ _)⟩
  simpa only [heightPolynomial,workPolynomial,BinaryFamilyArithmetic.heightPolynomial_eval,
    BinaryFamilyArithmetic.workPolynomial_eval] using
    BinaryFamilyArithmetic.multiply_bounds order base (H.eval security) (W.eval security) programs first second hf hs arity colors centers hc hd

end
end CurrentAFT.BinaryFamilyProductClosure

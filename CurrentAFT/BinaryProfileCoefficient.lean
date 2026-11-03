import CurrentAFT.BinaryFirstCoefficient
import CurrentAFT.BinaryProfileLookup
import CurrentAFT.BinaryRootSingleton

/-! # A generated palette profile inserted in the actual degree-one fiber -/
namespace CurrentAFT.BinaryProfileCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (security order : ℕ) (primary : Bool)
    (profile : Fin (BinaryProfileLookup.colors security) → RationalResult) : CoefficientProgram order :=
  BinaryFirstCoefficient.current order
    (if primary then BinaryProfileLookup.current security profile else BinaryRootSingleton.zeroProfile)
    (if primary then BinaryRootSingleton.zeroProfile else BinaryProfileLookup.current security profile)

theorem current_value (security order : ℕ) (primary : Bool)
    (profile : Fin (BinaryProfileLookup.colors security) → RationalResult) (ideal : ℕ → ℚ)
    (hvalue : ∀ color, (profile color).data.decode=ideal color.val)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (current security order primary profile arity colors centers).value.decode=
      BinaryRootSingleton.normalized security order
        (RationalBackgroundTable.firstTable order (if primary then ideal else fun _ => 0)
          (if primary then fun _ => 0 else ideal)) arity colors.get centers.get := by
  cases primary <;> unfold current <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [BinaryFirstCoefficient.current_value order _ _ (fun _ => 0)
      (fun output => ideal (output%BinaryProfileLookup.colors security)) (fun _ => zero_value)
      (fun output => BinaryProfileLookup.current_value security profile ideal hvalue output)]
    unfold BinaryRootSingleton.normalized RationalFamilyProductProgram.pullback RationalBackgroundTable.firstTable
    split_ifs <;> rfl
  · rw [BinaryFirstCoefficient.current_value order _ _
      (fun output => ideal (output%BinaryProfileLookup.colors security)) (fun _ => 0)
      (fun output => BinaryProfileLookup.current_value security profile ideal hvalue output) (fun _ => zero_value)]
    unfold BinaryRootSingleton.normalized RationalFamilyProductProgram.pullback RationalBackgroundTable.firstTable
    split_ifs <;> rfl

noncomputable section
def heightPolynomial (profileBits : Polynomial ℕ) : Polynomial ℕ := BinaryProfileLookup.heightPolynomial profileBits
def workPolynomial (order : ℕ) (profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (30*order+51)+BinaryProfileLookup.workPolynomial profileBits profileWork

theorem current_bounds (security order : ℕ) (primary : Bool) (profileBits profileWork : Polynomial ℕ)
    (profile : Fin (BinaryProfileLookup.colors security) → RationalResult)
    (hh : ∀ color, HeightBound (profile color).data.decode (profileBits.eval security))
    (hw : ∀ color, (profile color).work ≤ profileWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (current security order primary profile arity colors centers).value.decode ((heightPolynomial profileBits).eval security) ∧
      (current security order primary profile arity colors centers).work ≤ (workPolynomial order profileBits profileWork).eval security := by
  have hl (color : ℕ) (ho : color<BinaryProfileLookup.colors security) :=
    BinaryProfileLookup.current_bounds security profileBits profileWork profile color ho hh hw
  have hp (color : ℕ) (ho : color<BinaryProfileLookup.colors security) :
      HeightBound (BinaryProfileLookup.current security profile color).data.decode ((heightPolynomial profileBits).eval security) ∧
      (BinaryProfileLookup.current security profile color).work ≤ (BinaryProfileLookup.workPolynomial profileBits profileWork).eval security+1 :=
    ⟨(hl color ho).1,(hl color ho).2.trans (Nat.le_add_right _ _)⟩
  have hz (color : ℕ) (_ho : color<BinaryProfileLookup.colors security) :
      HeightBound (BinaryRootSingleton.zeroProfile color).data.decode ((heightPolynomial profileBits).eval security) ∧
      (BinaryRootSingleton.zeroProfile color).work ≤ (BinaryProfileLookup.workPolynomial profileBits profileWork).eval security+1 :=
    ⟨HeightBound.zero.mono (Nat.zero_le _),by simp only [BinaryRootSingleton.zeroProfile]; omega⟩
  have hfirst : ∀ color<BinaryProfileLookup.colors security,
      HeightBound ((if primary then BinaryProfileLookup.current security profile else BinaryRootSingleton.zeroProfile) color).data.decode
        ((heightPolynomial profileBits).eval security) ∧
      ((if primary then BinaryProfileLookup.current security profile else BinaryRootSingleton.zeroProfile) color).work ≤
        (BinaryProfileLookup.workPolynomial profileBits profileWork).eval security+1 := by
    cases primary
    · exact hz
    · exact hp
  have hbody : ∀ color<BinaryProfileLookup.colors security,
      HeightBound ((if primary then BinaryRootSingleton.zeroProfile else BinaryProfileLookup.current security profile) color).data.decode
        ((heightPolynomial profileBits).eval security) ∧
      ((if primary then BinaryRootSingleton.zeroProfile else BinaryProfileLookup.current security profile) color).work ≤
        (BinaryProfileLookup.workPolynomial profileBits profileWork).eval security+1 := by
    cases primary
    · exact hp
    · exact hz
  have h := BinaryFirstCoefficient.current_bounds order (BinaryProfileLookup.colors security)
    ((heightPolynomial profileBits).eval security) ((BinaryProfileLookup.workPolynomial profileBits profileWork).eval security+1)
    (if primary then BinaryProfileLookup.current security profile else BinaryRootSingleton.zeroProfile)
    (if primary then BinaryRootSingleton.zeroProfile else BinaryProfileLookup.current security profile) hfirst hbody
    arity colors centers hc hd
  constructor
  · exact h.1
  · unfold current
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    omega

end
end CurrentAFT.BinaryProfileCoefficient

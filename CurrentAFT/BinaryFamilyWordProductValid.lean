import CurrentAFT.BinaryFamilyWordProduct
import CurrentAFT.BinaryFamilyValidSemantics

/-! Valid-palette semantics for heterogeneous stored products. All inner
queries are gathers of the original palette words. -/
namespace CurrentAFT.BinaryFamilyWordProduct
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

 theorem product_value_valid (order base : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (count : ℕ) (tables : Fin count → CoefficientProgram order)
    (ideal : Fin count → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ index arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      (tables index arity colors centers).value.decode = ideal index arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < base) (hb : ∀ i, centers.get i < base) :
    (product order programs count tables arity colors centers).value.decode =
      RationalFamilyWordProduct.current order count ideal arity colors.get centers.get := by
  induction count generalizing arity colors centers with
  | zero => exact BinaryFamilyPower.unit_value order arity colors centers
  | succ count ih =>
    exact BinaryFamilyValidSemantics.multiply_value order base programs hcorrect hcomplete
      (product order programs count (fun index => tables index.succ)) (tables 0)
      (RationalFamilyWordProduct.current order count (fun index => ideal index.succ)) (ideal 0)
      (ih (fun index => tables index.succ) (fun index => ideal index.succ) (fun index => hvalue index.succ))
      (hvalue 0) arity colors centers hc hb

 theorem current_value_valid {Metadata : Type*} {count : ℕ} (order base : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (fallback : Metadata) (items : Vector Metadata count) (evaluate : Metadata → CoefficientProgram order)
    (ideal : Metadata → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ data arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      (evaluate data arity colors centers).value.decode = ideal data arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < base) (hb : ∀ i, centers.get i < base) :
    (current order programs fallback items evaluate arity colors centers).value.decode =
      RationalFamilyWordProduct.current order count (fun index => ideal (items.get index)) arity colors.get centers.get := by
  apply product_value_valid order base programs hcorrect hcomplete count _ _ _ arity colors centers hc hb
  intro index arity colors centers hc hb
  rw [storedTerm_value,hvalue _ _ _ _ hc hb]

end
end CurrentAFT.BinaryFamilyWordProduct

import CurrentAFT.BinaryRootSingleton

/-! # Modulo normalization commutes with every current coefficient operation -/
namespace CurrentAFT.BinaryRootSingleton
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct
set_option maxHeartbeats 800000

theorem normalized_point (security order : ℕ) (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → ℕ) (centers : Fin arity.val.2.val → ℕ)
    (hc : ∀ i, colors i<BinaryProfileLookup.colors security) (hd : ∀ i, centers i<BinaryProfileLookup.colors security) :
    normalized security order table arity colors centers=table arity colors centers := by
  unfold normalized RationalFamilyProductProgram.pullback
  have hcolors : ((fun color => color%BinaryProfileLookup.colors security) ∘ colors)=colors :=
    funext (fun index => Nat.mod_eq_of_lt (hc index))
  have hcenters : ((fun color => color%BinaryProfileLookup.colors security) ∘ centers)=centers :=
    funext (fun index => Nat.mod_eq_of_lt (hd index))
  rw [hcolors,hcenters]

theorem normalized_product (security order : ℕ) (first second : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    normalized security order (RationalFamilyProductProgram.product order first second)=
      RationalFamilyProductProgram.product order (normalized security order first) (normalized security order second) :=
  RationalFamilyProductProgram.pullback_product order _ _ first second

theorem normalized_reciprocal (security order : ℕ) (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    normalized security order (RationalFamilyProductProgram.reciprocal order table)=
      RationalFamilyProductProgram.reciprocal order (normalized security order table) :=
  RationalFamilyProductProgram.pullback_reciprocal order _ _ table

end CurrentAFT.BinaryRootSingleton

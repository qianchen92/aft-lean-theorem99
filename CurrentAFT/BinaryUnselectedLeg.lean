import CurrentAFT.BinaryLegMassResources
import CurrentAFT.BinaryLegFamilyResources
import CurrentAFT.BinaryRootSingletonResources
import CurrentAFT.BinaryNormalizedCoefficients
import CurrentAFT.BinaryFamilyValidSemantics
import CurrentAFT.RationalUnselectedLegProgram

/-! # The complete executed unselected leg, including its actual denominator -/
namespace CurrentAFT.BinaryUnselectedLeg
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev Descriptor := BinaryLegSelectedCoefficient.Entry

def higher (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (root : IntegerBits) : CoefficientProgram order :=
  BinaryLegFamily.higher security bits order fallback entries (BinaryLegMass.difference security bits root)

def positive (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8) : CoefficientProgram order :=
  BinaryLegFamily.positive security bits order fallback entries (BinaryLegMass.mean security bits)

def inverse (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor)
    (entries : Vector Descriptor 8) : CoefficientProgram order :=
  BinaryFamilyReciprocal.current order programs (positive security bits order fallback entries)

def numerator (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (root : IntegerBits) : CoefficientProgram order := fun arity colors centers =>
  let first := BinaryRootSingleton.first security bits order .attachment BinaryProfileLookup.zeroRoot root arity colors centers
  let higher := higher security bits order fallback entries root arity colors centers
  let result := RationalBits.add first.value higher.value
  ⟨result.data,first.work+higher.work+result.work+2⟩

def current (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor)
    (entries : Vector Descriptor 8) (root : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (numerator security bits order fallback entries root)
    (inverse security bits order programs fallback entries)

noncomputable section
open scoped Classical

theorem higher_value (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (ordering : Fin 8 ≃ Finset (Fin 3)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, BinaryLegSelectedCoefficient.Valid (entries.get index)) (root : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (higher security bits order fallback entries root arity colors centers).value.decode=
      RationalUnselectedLegProgram.higher security bits order root.decode arity colors.get centers.get :=
  BinaryLegFamily.higher_value security bits order fallback entries ordering hselected hvalid _ _
    (BinaryLegMass.difference_value security bits root) arity colors centers hc hd

theorem positive_value (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (ordering : Fin 8 ≃ Finset (Fin 3)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, BinaryLegSelectedCoefficient.Valid (entries.get index))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (positive security bits order fallback entries arity colors centers).value.decode=
      RationalUnselectedLegProgram.positive security bits order arity colors.get centers.get :=
  BinaryLegFamily.positive_value security bits order fallback entries ordering hselected hvalid _ _
    (BinaryLegMass.mean_value security bits) arity colors centers hc hd

theorem inverse_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (fallback : Descriptor) (entries : Vector Descriptor 8)
    (ordering : Fin 8 ≃ Finset (Fin 3)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, BinaryLegSelectedCoefficient.Valid (entries.get index))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (inverse security bits order programs fallback entries arity colors centers).value.decode=
      RationalUnselectedLegProgram.inverse security bits order arity colors.get centers.get :=
  BinaryFamilyValidSemantics.reciprocal_value order (BinaryFirstInverseProgram.colors security) programs hcorrect hcomplete _ _
    (positive_value security bits order fallback entries ordering hselected hvalid) arity colors centers hc hd

theorem numerator_value (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (ordering : Fin 8 ≃ Finset (Fin 3)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, BinaryLegSelectedCoefficient.Valid (entries.get index)) (root : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (numerator security bits order fallback entries root arity colors centers).value.decode=
      RationalUnselectedLegProgram.numerator security bits order root.decode arity colors.get centers.get := by
  rw [numerator,RationalBits.add_value,BinaryRootSingleton.first_value,
    BinaryRootSingleton.normalized_point security order _ arity colors.get centers.get hc hd,
    higher_value security bits order fallback entries ordering hselected hvalid root arity colors centers hc hd]
  rfl

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (fallback : Descriptor) (entries : Vector Descriptor 8)
    (ordering : Fin 8 ≃ Finset (Fin 3)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, BinaryLegSelectedCoefficient.Valid (entries.get index)) (root : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current security bits order programs fallback entries root arity colors centers).value.decode=
      RationalUnselectedLegProgram.current security bits order root.decode arity colors.get centers.get :=
  BinaryFamilyValidSemantics.multiply_value order (BinaryFirstInverseProgram.colors security) programs hcorrect hcomplete _ _ _ _
    (numerator_value security bits order fallback entries ordering hselected hvalid root)
    (inverse_value security bits order programs hcorrect hcomplete fallback entries ordering hselected hvalid) arity colors centers hc hd

end
end CurrentAFT.BinaryUnselectedLeg

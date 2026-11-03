import CurrentAFT.BinaryOrdinaryProfile
import CurrentAFT.BinaryProfileCoefficient
import CurrentAFT.BinaryRootSingletonResources
import CurrentAFT.RationalOrdinaryFamilyProgram

/-! # Executed ordinary hybrid numerator and its actual shared denominator -/
namespace CurrentAFT.BinaryOrdinaryCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def first (security bits order : ℕ) (source : Fin (colors security)) (root : IntegerBits) : CoefficientProgram order :=
  BinaryProfileCoefficient.current security order true (BinaryOrdinaryProfile.density security bits source root)

def bodyDelta (security bits : ℕ) (source output : Fin (colors security)) : RationalResult :=
  let reference := BinaryReferenceTables.current security bits
  let sourceValue := readVector zero reference.center source
  let point := BinaryMassLiftColumn.point source output
  let result := difference point.data sourceValue.value
  ⟨result.data,reference.work+sourceValue.work+point.work+result.work+4⟩

theorem bodyDelta_value (security bits : ℕ) (source output : Fin (colors security)) :
    (bodyDelta security bits source output).data.decode=
      WeightedPointKernelProgram.bodyDelta security bits source.val output.val := by
  simp only [bodyDelta,difference_value,readVector_value,BinaryReferenceTables.center_value,
    BinaryMassLiftColumn.point_value,Fin.ext_iff,WeightedPointKernelProgram.bodyDelta]

def bodyFirst (security bits order : ℕ) (source : Fin (colors security)) : CoefficientProgram order :=
  BinaryProfileCoefficient.current security order false (bodyDelta security bits source)

def atRoot (security bits order : ℕ) (programs : List (Entry order))
    (source : Fin (colors security)) (root : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (first security bits order source root)
    (BinaryRootSingleton.inverse security bits order programs .free BinaryProfileLookup.zeroRoot)

def independent (security bits order : ℕ) (programs : List (Entry order))
    (source : Fin (colors security)) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (bodyFirst security bits order source)
    (BinaryRootSingleton.inverse security bits order programs .free BinaryProfileLookup.zeroRoot)

theorem first_value (security bits order : ℕ) (source : Fin (colors security)) (root : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (first security bits order source root arity colors centers).value.decode =
      BinaryRootSingleton.normalized security order
        (RationalOrdinaryFamilyProgram.first security bits order source.val root.decode) arity colors.get centers.get :=
  BinaryProfileCoefficient.current_value security order true _ _ (BinaryOrdinaryProfile.density_value security bits source root)
    arity colors centers

theorem bodyFirst_value (security bits order : ℕ) (source : Fin (colors security))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (bodyFirst security bits order source arity colors centers).value.decode =
      BinaryRootSingleton.normalized security order
        (RationalOrdinaryFamilyProgram.bodyFirst security bits order source.val) arity colors.get centers.get :=
  BinaryProfileCoefficient.current_value security order false _ _ (bodyDelta_value security bits source) arity colors centers

noncomputable section
open scoped Classical

theorem atRoot_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (source : Fin (colors security)) (root : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (atRoot security bits order programs source root arity colors centers).value.decode =
      BinaryRootSingleton.normalized security order
        (RationalOrdinaryFamilyProgram.atRoot security bits order source.val root.decode) arity colors.get centers.get := by
  rw [atRoot,BinaryFamilyArithmetic.multiply_value order programs hcorrect hcomplete _ _ _ _
    (first_value security bits order source root)
    (BinaryRootSingleton.inverse_value security bits order programs hcorrect hcomplete .free BinaryProfileLookup.zeroRoot)]
  unfold BinaryRootSingleton.normalized RationalOrdinaryFamilyProgram.atRoot
  rw [RationalFamilyProductProgram.pullback_product]
  rfl

theorem independent_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (source : Fin (colors security))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (independent security bits order programs source arity colors centers).value.decode =
      BinaryRootSingleton.normalized security order
        (RationalOrdinaryFamilyProgram.independent security bits order source.val) arity colors.get centers.get := by
  rw [independent,BinaryFamilyArithmetic.multiply_value order programs hcorrect hcomplete _ _ _ _
    (bodyFirst_value security bits order source)
    (BinaryRootSingleton.inverse_value security bits order programs hcorrect hcomplete .free BinaryProfileLookup.zeroRoot)]
  unfold BinaryRootSingleton.normalized RationalOrdinaryFamilyProgram.independent
  rw [RationalFamilyProductProgram.pullback_product]
  rfl

end
end CurrentAFT.BinaryOrdinaryCoefficient

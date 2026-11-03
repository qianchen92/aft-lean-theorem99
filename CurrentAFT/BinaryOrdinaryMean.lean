import CurrentAFT.BinaryOrdinaryCoefficientResources
import CurrentAFT.BinaryRootSignedMass

/-! # The actual ordinary hybrid keeps the same root in its full numerator -/
namespace CurrentAFT.BinaryOrdinaryMean
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term (security bits order : ℕ) (programs : List (Entry order)) (source : Fin (colors security))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (root : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter root.val
  let probability := BinaryRootSignedMass.referenceEntry security bits root.val
  let column := BinaryOrdinaryCoefficient.atRoot security bits order programs source ⟨false,code.digits⟩ arity colors centers
  let result := RationalBits.multiply probability.data column.value
  ⟨result.data,code.work+probability.work+column.work+result.work+4⟩

def mean (security bits order : ℕ) (programs : List (Entry order)) (source : Fin (colors security)) : CoefficientProgram order :=
  fun arity colors centers =>
    let modulus := PublicParameterProgram.modulus security
    let result := sumFin modulus.count (term security bits order programs source arity colors centers)
    ⟨result.data,modulus.work+result.work+2⟩

def current (security bits order : ℕ) (programs : List (Entry order)) (source : Fin (colors security))
    (root : IntegerBits) : CoefficientProgram order :=
  fun arity colors centers =>
    let independent := BinaryOrdinaryCoefficient.independent security bits order programs source arity colors centers
    let atRoot := BinaryOrdinaryCoefficient.atRoot security bits order programs source root arity colors centers
    let average := mean security bits order programs source arity colors centers
    let combined := RationalBits.add independent.value atRoot.value
    let result := difference combined.data average.value
    ⟨result.data,independent.work+atRoot.work+average.work+combined.work+result.work+5⟩

noncomputable section
open scoped Classical

theorem term_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (source : Fin (colors security))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (root : Fin (BinaryFirstInverseProgram.colors security)) :
    (term security bits order programs source arity colors centers root).data.decode=
      RootSignedMassProgram.referenceEntry security bits root.val*
        BinaryRootSingleton.normalized security order (RationalOrdinaryFamilyProgram.atRoot security bits order source.val root.val)
          arity colors.get centers.get := by
  simp only [term,RationalBits.multiply_value,BinaryRootSignedMass.referenceEntry_value,
    BinaryOrdinaryCoefficient.atRoot_value security bits order programs hcorrect hcomplete,
    IntegerBits.decode,signedValue,Bool.false_eq_true,if_false,canonicalCounter_value]

theorem mean_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (source : Fin (colors security))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (mean security bits order programs source arity colors centers).value.decode=
      BinaryRootSingleton.normalized security order (RationalOrdinaryFamilyProgram.mean security bits order source.val)
        arity colors.get centers.get := by
  simp only [mean,sumFin_value,term_value security bits order programs hcorrect hcomplete]
  rfl

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (source : Fin (colors security)) (root : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (current security bits order programs source root arity colors centers).value.decode=
      BinaryRootSingleton.normalized security order (RationalOrdinaryFamilyProgram.current security bits order source.val root.decode)
        arity colors.get centers.get := by
  simp only [current,difference_value,RationalBits.add_value,
    BinaryOrdinaryCoefficient.independent_value security bits order programs hcorrect hcomplete,
    BinaryOrdinaryCoefficient.atRoot_value security bits order programs hcorrect hcomplete,
    mean_value security bits order programs hcorrect hcomplete]
  rfl

end
end CurrentAFT.BinaryOrdinaryMean

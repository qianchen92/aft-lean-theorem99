import CurrentAFT.BinaryRootDensityResources
import CurrentAFT.BinaryProfileLookup
import CurrentAFT.BinaryFirstCoefficient
import CurrentAFT.BinaryFamilyReciprocal
import CurrentAFT.RationalSingletonProgram

/-! # The actual pure-primary singleton and its finite reciprocal are executed -/
namespace CurrentAFT.BinaryRootSingleton
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def zeroProfile (_color : ℕ) : RationalResult := ⟨zero,1⟩

def first (security bits order : ℕ) (role : BodyRole) (queue root : IntegerBits) : CoefficientProgram order :=
  BinaryFirstCoefficient.current order
    (BinaryProfileLookup.current security (BinaryRootProfile.firstDensity security bits role queue root)) zeroProfile

def meanFirst (security bits order : ℕ) (role : BodyRole) (queue : IntegerBits) : CoefficientProgram order :=
  BinaryFirstCoefficient.current order
    (BinaryProfileLookup.current security (BinaryRootProfile.meanDensity security bits role queue)) zeroProfile

def positive (security bits order : ℕ) (role : BodyRole) (queue : IntegerBits) : CoefficientProgram order :=
  fun arity colors centers =>
    let unit := BinaryFamilyPower.unit order arity colors centers
    let first := meanFirst security bits order role queue arity colors centers
    let result := RationalBits.add unit.value first.value
    ⟨result.data,unit.work+first.work+result.work+2⟩

def inverse (security bits order : ℕ) (programs : List (Entry order)) (role : BodyRole) (queue : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyReciprocal.current order programs (positive security bits order role queue)

def current (security bits order : ℕ) (programs : List (Entry order)) (role : BodyRole)
    (queue root : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (first security bits order role queue root)
    (inverse security bits order programs role queue)

def normalized (security order : ℕ) (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.pullback order (fun color => color%BinaryProfileLookup.colors security)
    (fun color => color%BinaryProfileLookup.colors security) table

theorem first_value (security bits order : ℕ) (role : BodyRole) (queue root : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (first security bits order role queue root arity colors centers).value.decode =
      normalized security order (RationalSingletonProgram.first security bits order role queue.decode root.decode)
        arity colors.get centers.get := by
  rw [first,BinaryFirstCoefficient.current_value order _ _
    (fun output => RationalRootProfileProgram.firstDensity security bits role queue.decode root.decode
      (output%BinaryProfileLookup.colors security)) (fun _ => 0)
    (fun output => BinaryProfileLookup.current_value security _ _
      (BinaryRootProfile.firstDensity_value security bits role queue root) output)
    (fun _ => zero_value)]
  unfold normalized RationalSingletonProgram.first RationalFamilyProductProgram.pullback
    RationalBackgroundTable.firstTable
  split_ifs <;> rfl

theorem meanFirst_value (security bits order : ℕ) (role : BodyRole) (queue : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (meanFirst security bits order role queue arity colors centers).value.decode =
      normalized security order (RationalBackgroundTable.firstTable order
        (RationalRootProfileProgram.meanDensity security bits role queue.decode) (fun _ => 0))
        arity colors.get centers.get := by
  rw [meanFirst,BinaryFirstCoefficient.current_value order _ _
    (fun output => RationalRootProfileProgram.meanDensity security bits role queue.decode
      (output%BinaryProfileLookup.colors security)) (fun _ => 0)
    (fun output => BinaryProfileLookup.current_value security _ _
      (BinaryRootProfile.meanDensity_value security bits role queue) output)
    (fun _ => zero_value)]
  unfold normalized RationalFamilyProductProgram.pullback RationalBackgroundTable.firstTable
  split_ifs <;> rfl

theorem positive_value (security bits order : ℕ) (role : BodyRole) (queue : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (positive security bits order role queue arity colors centers).value.decode =
      normalized security order (RationalSingletonProgram.positive security bits order role queue.decode)
        arity colors.get centers.get := by
  simp only [positive,RationalBits.add_value,BinaryFamilyPower.unit_value,meanFirst_value]
  unfold normalized RationalSingletonProgram.positive RationalFamilyProductProgram.pullback
  simp only [Pi.add_apply,RationalFamilyProductProgram.unit]

noncomputable section
open scoped Classical

theorem inverse_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (role : BodyRole) (queue : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (inverse security bits order programs role queue arity colors centers).value.decode =
      normalized security order (RationalSingletonProgram.inverse security bits order role queue.decode)
        arity colors.get centers.get := by
  rw [inverse,BinaryFamilyReciprocal.current_value order programs hcorrect hcomplete _ _
    (positive_value security bits order role queue)]
  unfold normalized RationalSingletonProgram.inverse
  rw [RationalFamilyProductProgram.pullback_reciprocal]

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (role : BodyRole) (queue root : IntegerBits)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (current security bits order programs role queue root arity colors centers).value.decode =
      normalized security order (RationalSingletonProgram.current security bits order role queue.decode root.decode)
        arity colors.get centers.get := by
  rw [current,BinaryFamilyArithmetic.multiply_value order programs hcorrect hcomplete _ _ _ _
    (first_value security bits order role queue root) (inverse_value security bits order programs hcorrect hcomplete role queue)]
  unfold normalized RationalSingletonProgram.current
  rw [RationalFamilyProductProgram.pullback_product]

end
end CurrentAFT.BinaryRootSingleton

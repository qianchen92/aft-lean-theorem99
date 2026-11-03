import CurrentAFT.BinaryFirstFamily
import CurrentAFT.BinaryFamilyArithmetic

/-! # First-degree table dispatch with charged natural-index reads -/
namespace CurrentAFT.BinaryFirstCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (order : ℕ) (primary body : ℕ → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let primaryShape := BinaryFirstFamily.primaryGuard arity.val.1.val arity.val.2.val
    let bodyShape := BinaryFirstFamily.primaryGuard arity.val.2.val arity.val.1.val
    if hp : primaryShape.value=true then
      let input := readVector 0 colors ⟨0,by have := (BinaryFirstFamily.primaryGuard_value _ _).mp hp; omega⟩
      let result := primary input.value
      ⟨result.data,primaryShape.work+bodyShape.work+input.work+result.work+5⟩
    else if hb : bodyShape.value=true then
      let center := readVector 0 centers ⟨0,by have := (BinaryFirstFamily.primaryGuard_value _ _).mp hb; omega⟩
      let result := body center.value
      ⟨result.data,primaryShape.work+bodyShape.work+center.work+result.work+5⟩
    else ⟨zero,primaryShape.work+bodyShape.work+3⟩

theorem current_value (order : ℕ) (primary body : ℕ → RationalResult) (primaryValue bodyValue : ℕ → ℚ)
    (hp : ∀ color, (primary color).data.decode=primaryValue color)
    (hb : ∀ color, (body color).data.decode=bodyValue color)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (current order primary body arity colors centers).value.decode=
      RationalBackgroundTable.firstTable order primaryValue bodyValue arity colors.get centers.get := by
  by_cases hprimary : (BinaryFirstFamily.primaryGuard arity.val.1.val arity.val.2.val).value=true
  · have hs := (BinaryFirstFamily.primaryGuard_value _ _).mp hprimary
    simp only [current,dif_pos hprimary,readVector_value,hp,RationalBackgroundTable.firstTable,dif_pos hs]
  · have hn : ¬(arity.val.1.val=1 ∧ arity.val.2.val=0) := fun hs => hprimary ((BinaryFirstFamily.primaryGuard_value _ _).mpr hs)
    by_cases hbody : (BinaryFirstFamily.primaryGuard arity.val.2.val arity.val.1.val).value=true
    · have hs := (BinaryFirstFamily.primaryGuard_value _ _).mp hbody
      simp only [current,dif_neg hprimary,dif_pos hbody,readVector_value,hb,RationalBackgroundTable.firstTable,
        dif_neg hn,dif_pos (And.intro hs.2 hs.1)]
    · have hn' : ¬(arity.val.1.val=0 ∧ arity.val.2.val=1) := fun hs => hbody ((BinaryFirstFamily.primaryGuard_value _ _).mpr ⟨hs.2,hs.1⟩)
      simp only [current,dif_neg hprimary,dif_neg hbody,zero_value,RationalBackgroundTable.firstTable,dif_neg hn,dif_neg hn']

theorem current_bounds (order base bits budget : ℕ) (primary body : ℕ → RationalResult)
    (hp : ∀ color<base, HeightBound (primary color).data.decode bits ∧ (primary color).work≤budget)
    (hb : ∀ color<base, HeightBound (body color).data.decode bits ∧ (body color).work≤budget)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<base) (hd : ∀ i, centers.get i<base) :
    HeightBound (current order primary body arity colors centers).value.decode bits ∧
      (current order primary body arity colors centers).work≤30*order+budget+50 := by
  have wp := BinaryFirstFamily.primaryGuard_work arity.val.1.val arity.val.2.val
  have wb := BinaryFirstFamily.primaryGuard_work arity.val.2.val arity.val.1.val
  have hr := arity.val.1.isLt
  have hs := arity.val.2.isLt
  by_cases hprimary : (BinaryFirstFamily.primaryGuard arity.val.1.val arity.val.2.val).value=true
  · let slot : Fin arity.val.1.val := ⟨0,by have := (BinaryFirstFamily.primaryGuard_value _ _).mp hprimary; omega⟩
    have hv := hp (colors.get slot) (hc slot)
    have wi := readVector_work 0 colors slot
    dsimp only [slot] at hv wi
    simp only [current,dif_pos hprimary,readVector_value]
    exact ⟨hv.1,by change _≤_ at wi; omega⟩
  · by_cases hbody : (BinaryFirstFamily.primaryGuard arity.val.2.val arity.val.1.val).value=true
    · let slot : Fin arity.val.2.val := ⟨0,by have := (BinaryFirstFamily.primaryGuard_value _ _).mp hbody; omega⟩
      have hv := hb (centers.get slot) (hd slot)
      have wi := readVector_work 0 centers slot
      dsimp only [slot] at hv wi
      simp only [current,dif_neg hprimary,dif_pos hbody,readVector_value]
      exact ⟨hv.1,by change _≤_ at wi; omega⟩
    · simp only [current,dif_neg hprimary,dif_neg hbody,zero_value]
      exact ⟨HeightBound.zero.mono (Nat.zero_le _),by omega⟩

end CurrentAFT.BinaryFirstCoefficient

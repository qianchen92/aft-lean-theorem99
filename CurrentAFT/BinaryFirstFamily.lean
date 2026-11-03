import CurrentAFT.BinaryBackgroundBody
import CurrentAFT.RationalBackgroundTable

/-! # Executed first-primary/first-body coefficient-table dispatch -/
namespace CurrentAFT.BinaryFirstFamily
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter PublicParameterProgram.modulus

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def first (security : ℕ) : Fin (colors security) :=
  ⟨0,by rw [colors,BinaryFirstInverseProgram.colors,PublicParameterProgram.modulus_value]
        exact (Parameters.modulus_spec security).2.pos⟩

def primaryGuard (r s : ℕ) : CountedValue Bool :=
  let positive := lessCounter 0 r
  let belowTwo := lessCounter r 2
  let bodyZero := lessCounter s 1
  ⟨positive.value && belowTwo.value && bodyZero.value,positive.work+belowTwo.work+bodyZero.work+4⟩

theorem primaryGuard_value (r s : ℕ) : (primaryGuard r s).value=true ↔ r=1 ∧ s=0 := by
  simp only [primaryGuard,Bool.and_eq_true,lessCounter_value]
  omega

theorem primaryGuard_work (r s : ℕ) : (primaryGuard r s).work≤6*r+3*s+19 := by
  have hp := lessCounter_work 0 r
  have ht := lessCounter_work r 2
  have hb := lessCounter_work s 1
  change _+_+_+4≤_
  omega

def current (security r s : ℕ) (primary body : Fin (colors security)→RationalResult)
    (inputs : Vector (Fin (colors security)) r) (centers : Vector (Fin (colors security)) s) : RationalResult :=
  let primaryShape := primaryGuard r s
  let bodyShape := primaryGuard s r
  if hp : primaryShape.value=true then
    let input := readVector (first security) inputs ⟨0,by have := (primaryGuard_value r s).mp hp; omega⟩
    let result := primary input.value
    ⟨result.data,primaryShape.work+bodyShape.work+input.work+result.work+5⟩
  else if hb : bodyShape.value=true then
    let center := readVector (first security) centers ⟨0,by have := (primaryGuard_value s r).mp hb; omega⟩
    let result := body center.value
    ⟨result.data,primaryShape.work+bodyShape.work+center.work+result.work+5⟩
  else ⟨zero,primaryShape.work+bodyShape.work+3⟩

theorem current_value (security order : ℕ) (arity : TruncatedArity order)
    (primary body : Fin (colors security)→RationalResult) (primaryValue bodyValue : ℕ→ℚ)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val)
    (hp : ∀ color, (primary color).data.decode=primaryValue color.val)
    (hb : ∀ color, (body color).data.decode=bodyValue color.val) :
    (current security arity.val.1.val arity.val.2.val primary body inputs centers).data.decode=
      RationalBackgroundTable.firstTable order primaryValue bodyValue arity
        (fun index => (inputs.get index).val) (fun index => (centers.get index).val) := by
  by_cases hprimary : (primaryGuard arity.val.1.val arity.val.2.val).value=true
  · have hs := (primaryGuard_value _ _).mp hprimary
    simp only [current,dif_pos hprimary,readVector_value,hp,RationalBackgroundTable.firstTable,dif_pos hs]
  · have hn : ¬(arity.val.1.val=1 ∧ arity.val.2.val=0) := fun hs => hprimary ((primaryGuard_value _ _).mpr hs)
    by_cases hbody : (primaryGuard arity.val.2.val arity.val.1.val).value=true
    · have hs := (primaryGuard_value _ _).mp hbody
      simp only [current,dif_neg hprimary,dif_pos hbody,readVector_value,hb,RationalBackgroundTable.firstTable,
        dif_neg hn,dif_pos (And.intro hs.2 hs.1)]
    · have hn' : ¬(arity.val.1.val=0 ∧ arity.val.2.val=1) := fun hs => hbody ((primaryGuard_value _ _).mpr ⟨hs.2,hs.1⟩)
      simp only [current,dif_neg hprimary,dif_neg hbody,zero_value,RationalBackgroundTable.firstTable,dif_neg hn,dif_neg hn']

def work (r s primaryWork bodyWork : ℕ) := 15*(r+s)+primaryWork+bodyWork+50

theorem current_bounds (security r s : ℕ) (primary body : Fin (colors security)→RationalResult)
    (inputs : Vector (Fin (colors security)) r) (centers : Vector (Fin (colors security)) s)
    (primaryBits bodyBits primaryWork bodyWork : ℕ)
    (hp : ∀ color, HeightBound (primary color).data.decode primaryBits)
    (hb : ∀ color, HeightBound (body color).data.decode bodyBits)
    (wp : ∀ color, (primary color).work≤primaryWork) (wb : ∀ color, (body color).work≤bodyWork) :
    HeightBound (current security r s primary body inputs centers).data.decode (primaryBits+bodyBits) ∧
      (current security r s primary body inputs centers).work≤work r s primaryWork bodyWork := by
  have wpShape := primaryGuard_work r s
  have wbShape := primaryGuard_work s r
  by_cases hprimary : (primaryGuard r s).value=true
  · let slot : Fin r := ⟨0,by have := (primaryGuard_value r s).mp hprimary; omega⟩
    let input := readVector (first security) inputs slot
    have hi := readVector_work (first security) inputs slot
    have hw := wp input.value
    constructor
    · simpa only [current,dif_pos hprimary] using (hp input.value).mono (Nat.le_add_right primaryBits bodyBits)
    · rw [current,dif_pos hprimary]
      change (primaryGuard r s).work+(primaryGuard s r).work+input.work+(primary input.value).work+5≤_
      unfold work
      change input.work≤_ at hi
      omega
  · by_cases hbody : (primaryGuard s r).value=true
    · let slot : Fin s := ⟨0,by have := (primaryGuard_value s r).mp hbody; omega⟩
      let center := readVector (first security) centers slot
      have hi := readVector_work (first security) centers slot
      have hw := wb center.value
      constructor
      · simpa only [current,dif_neg hprimary,dif_pos hbody] using (hb center.value).mono (Nat.le_add_left bodyBits primaryBits)
      · rw [current,dif_neg hprimary,dif_pos hbody]
        change (primaryGuard r s).work+(primaryGuard s r).work+center.work+(body center.value).work+5≤_
        unfold work
        change center.work≤_ at hi
        omega
    · constructor
      · simp only [current,dif_neg hprimary,dif_neg hbody,zero_value]
        exact HeightBound.zero.mono (Nat.zero_le _)
      · rw [current,dif_neg hprimary,dif_neg hbody]
        change (primaryGuard r s).work+(primaryGuard s r).work+3≤_
        unfold work
        omega

end CurrentAFT.BinaryFirstFamily

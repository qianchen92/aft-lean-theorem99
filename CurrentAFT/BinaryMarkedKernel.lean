import CurrentAFT.BinaryDiffuseProgram
import CurrentAFT.LocalMarkedProgram
import AFT.BinarySignedShiftSum

/-! # The actual marked anchor on Boolean-list operands

The negative anchor is traversed in reverse order. This preserves its
uniform index law and allows both directions to use the same increasing
integer interval, including the genuine `toNat` output convention.
-/
namespace CurrentAFT.BinaryMarkedKernel
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] binaryBaselineStart canonicalCounter signedAdd

def companion (colors width primary left right index : ℕ) (choice sourceSign : Bool)
    (source : List Bool) : SignedResult :=
  let baseline := binaryBaselineStart colors width primary (!choice)
  let colorCode := canonicalCounter colors
  let primaryCode := canonicalCounter primary
  let indexCode := canonicalCounter index
  let leftCode := canonicalCounter left
  let rightCode := canonicalCounter right
  let last := signedAdd false true colorCode.digits [true]
  let anchor := signedAdd last.negative true last.digits primaryCode.digits
  let start := signedAdd anchor.negative baseline.negative anchor.digits baseline.digits
  let point := signedAdd start.negative false start.digits indexCode.digits
  let blur := signedAdd false true leftCode.digits rightCode.digits
  let shifted := signedAdd point.negative blur.negative point.digits blur.digits
  let result := signedAdd shifted.negative (!sourceSign) shifted.digits source
  ⟨result.negative, result.digits, baseline.work + colorCode.work + primaryCode.work + indexCode.work +
    leftCode.work + rightCode.work + last.work + anchor.work + start.work + point.work +
    blur.work + shifted.work + result.work + 13⟩

theorem companion_value (colors width primary left right index : ℕ) (choice sourceSign : Bool)
    (source : List Bool) :
    signedValue (companion colors width primary left right index choice sourceSign source).negative
      (companion colors width primary left right index choice sourceSign source).digits =
      (colors : ℤ)-1-primary +
        (if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1) +
        index + ((left : ℤ)-right) - signedValue sourceSign source := by
  unfold companion
  rw [signedAdd_value, BinaryTrimmedPair.signed_negate, signedAdd_value, signedAdd_value,
    signedAdd_value, signedAdd_value, BinaryDiffuseProgram.baseline_value, signedAdd_value, signedAdd_value]
  simp only [signedValue, Bool.false_eq_true, if_false, if_true, canonicalCounter_value]
  norm_num [value]
  ring

def companionWork (bound : ℕ) : ℕ := 1000*(3*bound+2)^2 + 5*(50*(bound+1)^2) + 300*(bound+10)

theorem companion_bounds (colors width primary left right index : ℕ) (choice sourceSign : Bool)
    (source : List Bool) (bound : ℕ) (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hl : left ≤ bound) (hr : right ≤ bound) (hi : index ≤ bound) (hs : source.length ≤ bound) :
    (companion colors width primary left right index choice sourceSign source).digits.length ≤ 2*bound+7 ∧
      (companion colors width primary left right index choice sourceSign source).work ≤ companionWork bound := by
  let baseline := binaryBaselineStart colors width primary (!choice)
  let colorCode := canonicalCounter colors
  let primaryCode := canonicalCounter primary
  let indexCode := canonicalCounter index
  let leftCode := canonicalCounter left
  let rightCode := canonicalCounter right
  let last := signedAdd false true colorCode.digits [true]
  let anchor := signedAdd last.negative true last.digits primaryCode.digits
  let start := signedAdd anchor.negative baseline.negative anchor.digits baseline.digits
  let point := signedAdd start.negative false start.digits indexCode.digits
  let blur := signedAdd false true leftCode.digits rightCode.digits
  let shifted := signedAdd point.negative blur.negative point.digits blur.digits
  have code_length (number : ℕ) (hn : number ≤ bound) : (canonicalCounter number).digits.length ≤ bound := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := number))).trans hn
  have code_work (number : ℕ) (hn : number ≤ bound) : (canonicalCounter number).work ≤ 50*(bound+1)^2 :=
    (canonicalCounter_work number).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have hc : colorCode.digits.length ≤ bound := code_length colors hq
  have hp' : primaryCode.digits.length ≤ bound := code_length primary hp
  have hi' : indexCode.digits.length ≤ bound := code_length index hi
  have hl' : leftCode.digits.length ≤ bound := code_length left hl
  have hr' : rightCode.digits.length ≤ bound := code_length right hr
  have b0 : baseline.digits.length ≤ 2*bound+2 := (binaryBaselineStart_length _ _ _ _).trans (by omega)
  have b1 : last.digits.length ≤ bound+2 := (signedAdd_length _ _ _ _).trans (by have := code_length colors hq; simp only [List.length_cons, List.length_nil]; omega)
  have b2 : anchor.digits.length ≤ bound+3 := (signedAdd_length _ _ _ _).trans (by have := code_length primary hp; omega)
  have b3 : start.digits.length ≤ 2*bound+4 := (signedAdd_length _ _ _ _).trans (by omega)
  have b4 : point.digits.length ≤ 2*bound+5 := (signedAdd_length _ _ _ _).trans (by have := code_length index hi; omega)
  have b5 : blur.digits.length ≤ bound+1 := (signedAdd_length _ _ _ _).trans (by have := code_length left hl; have := code_length right hr; omega)
  have b6 : shifted.digits.length ≤ 2*bound+6 := (signedAdd_length _ _ _ _).trans (by omega)
  have b7 := signedAdd_length shifted.negative (!sourceSign) shifted.digits source
  have wb : baseline.work ≤ 1000*(3*bound+2)^2 :=
    (binaryBaselineStart_work colors width primary (!choice)).trans
      (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (by omega) 2))
  have wc : colorCode.work ≤ 50*(bound+1)^2 := code_work colors hq
  have wp : primaryCode.work ≤ 50*(bound+1)^2 := code_work primary hp
  have wi : indexCode.work ≤ 50*(bound+1)^2 := code_work index hi
  have wl : leftCode.work ≤ 50*(bound+1)^2 := code_work left hl
  have wr : rightCode.work ≤ 50*(bound+1)^2 := code_work right hr
  have w1 : last.work ≤ 20*(bound+1)+8 := (signedAdd_work _ _ _ _).trans (by have := code_length colors hq; simp only [List.length_cons, List.length_nil]; omega)
  have w2 : anchor.work ≤ 20*(bound+2)+8 := (signedAdd_work _ _ _ _).trans (by have := code_length primary hp; omega)
  have w3 : start.work ≤ 20*(2*bound+3)+8 := (signedAdd_work _ _ _ _).trans (by omega)
  have w4 : point.work ≤ 20*(2*bound+4)+8 := (signedAdd_work _ _ _ _).trans (by have := code_length index hi; omega)
  have w5 : blur.work ≤ 20*bound+8 := (signedAdd_work _ _ _ _).trans (by have := code_length left hl; have := code_length right hr; omega)
  have w6 : shifted.work ≤ 20*(2*bound+5)+8 := (signedAdd_work _ _ _ _).trans (by omega)
  have w7 := signedAdd_work shifted.negative (!sourceSign) shifted.digits source
  constructor
  · change (signedAdd shifted.negative (!sourceSign) shifted.digits source).digits.length ≤ 2*bound+7
    omega
  · change baseline.work + colorCode.work + primaryCode.work + indexCode.work + leftCode.work +
      rightCode.work + last.work + anchor.work + start.work + point.work + blur.work + shifted.work +
      (signedAdd shifted.negative (!sourceSign) shifted.digits source).work + 13 ≤ _
    unfold companionWork
    omega

def point (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) (index : Fin width) : RationalResult :=
  let color := canonicalCounter primary
  let output := companion colors width primary left right index.val choice sourceSign source
  let primaryMatch := signedEqual false false color.digits first
  let companionMatch := signedEqual false false (nonnegativeDigits output.negative output.digits) second
  ⟨if primaryMatch.value && companionMatch.value then one else zero,
    color.work + output.work + primaryMatch.work + companionMatch.work + 6⟩

theorem point_value (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) (index : Fin width) :
    (point colors width primary left right choice sourceSign source first second index).data.decode =
      if primary = value first ∧
        ((colors : ℤ)-1-primary +
          (if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1) +
          index.val + ((left : ℤ)-right) - signedValue sourceSign source).toNat = value second
      then 1 else 0 := by
  have h1 : (signedEqual false false (canonicalCounter primary).digits first).value = true ↔ primary = value first := by
    rw [signedEqual_value]
    simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value, Int.natCast_inj]
  have h2 : (signedEqual false false
      (nonnegativeDigits (companion colors width primary left right index.val choice sourceSign source).negative
        (companion colors width primary left right index.val choice sourceSign source).digits) second).value = true ↔
      ((colors : ℤ)-1-primary +
        (if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1) +
        index.val + ((left : ℤ)-right) - signedValue sourceSign source).toNat = value second := by
    rw [signedEqual_value]
    simp only [signedValue, Bool.false_eq_true, if_false, Int.natCast_inj]
    rw [nonnegativeDigits_value, companion_value]
    rfl
  simp only [point, Bool.and_eq_true, h1, h2]
  split_ifs <;> simp only [one_value, zero_value]

def pointWork (bound : ℕ) : ℕ :=
  50*(bound+1)^2 + companionWork bound + (48*bound+39) + (48*(2*bound+7)+39) + 6

theorem point_bounds (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) (index : Fin width) (bound : ℕ)
    (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hl : left ≤ bound) (hr : right ≤ bound) (hs : source.length ≤ bound)
    (hf : first.length ≤ bound) (ht : second.length ≤ bound) :
    HeightBound (point colors width primary left right choice sourceSign source first second index).data.decode 0 ∧
      (point colors width primary left right choice sourceSign source first second index).work ≤ pointWork bound := by
  have hi : index.val ≤ bound := index.isLt.le.trans hw
  have ho := companion_bounds colors width primary left right index.val choice sourceSign source bound hq hw hp hl hr hi hs
  have hc : (canonicalCounter primary).digits.length ≤ bound := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := primary))).trans hp
  have wc : (canonicalCounter primary).work ≤ 50*(bound+1)^2 :=
    (canonicalCounter_work primary).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have wp := signedEqual_work false false (canonicalCounter primary).digits first
  have wt := signedEqual_work false false
    (nonnegativeDigits (companion colors width primary left right index.val choice sourceSign source).negative
      (companion colors width primary left right index.val choice sourceSign source).digits) second
  have hn := nonnegativeDigits_length (companion colors width primary left right index.val choice sourceSign source).negative
    (companion colors width primary left right index.val choice sourceSign source).digits
  constructor
  · rw [point_value]
    split_ifs <;> first | exact HeightBound.one | exact HeightBound.zero
  · unfold point pointWork
    dsimp only
    omega

def coin (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  let total := sumFin width (point colors width primary left right choice sourceSign source first second)
  let denominator := ofCounter width
  let result := quotient total.data denominator.data
  ⟨result.data, total.work + denominator.work + result.work + 3⟩

theorem point_reindex (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) (index : Fin width) :
    (point colors width primary left right choice sourceSign source first second index).data.decode =
      LocalMarkedProgram.pointEntry colors width primary (signedValue sourceSign source) ((left : ℤ)-right) choice
        (if LocalDiffuseProgram.direction colors primary choice then index else index.rev) (value first) (value second) := by
  rw [point_value]
  unfold LocalMarkedProgram.pointEntry LocalMarkedProgram.companionValue
  have hv : (colors : ℤ)-1-primary +
      (if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1) +
      index.val + ((left : ℤ)-right) - signedValue sourceSign source =
    (colors : ℤ)-1-primary +
      (if LocalDiffuseProgram.direction colors primary choice then
        (width : ℤ)+(if LocalDiffuseProgram.direction colors primary choice then index else index.rev).val
        else -((width : ℤ)+(if LocalDiffuseProgram.direction colors primary choice then index else index.rev).val)) +
      ((left : ℤ)-right) - signedValue sourceSign source := by
    by_cases hd : LocalDiffuseProgram.direction colors primary choice = true
    · simp only [hd, if_true]
      ring
    · simp only [hd, Bool.false_eq_true, if_false, Fin.val_rev]
      have hi := index.isLt
      omega
  rw [hv]

theorem coin_value (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) :
    (coin colors width primary left right choice sourceSign source first second).data.decode =
      LocalMarkedProgram.coinEntry colors width primary (signedValue sourceSign source) ((left : ℤ)-right) choice
        (value first) (value second) := by
  have hsum : (∑ index : Fin width,
      (point colors width primary left right choice sourceSign source first second index).data.decode) =
      ∑ index : Fin width, LocalMarkedProgram.pointEntry colors width primary (signedValue sourceSign source)
        ((left : ℤ)-right) choice index (value first) (value second) := by
    simp only [point_reindex]
    by_cases hd : LocalDiffuseProgram.direction colors primary choice = true
    · simp only [hd, if_true]
    · simp only [hd, Bool.false_eq_true, if_false]
      exact Equiv.sum_comp (Fin.revPerm (n := width)) (fun index =>
        LocalMarkedProgram.pointEntry colors width primary (signedValue sourceSign source)
          ((left : ℤ)-right) choice index (value first) (value second))
  simp only [coin, quotient_value, sumFin_value, ofCounter_value, LocalMarkedProgram.coinEntry]
  rw [hsum]
  ring

def coinWork (width bound : ℕ) : ℕ :=
  width*(pointWork bound + primitiveWorkBound (width+1)+2)+2 +
    60*(width+1)^2 + (2*primitiveWorkBound width+2) + 3

theorem coin_bounds (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) (bound : ℕ)
    (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hl : left ≤ bound) (hr : right ≤ bound) (hs : source.length ≤ bound)
    (hf : first.length ≤ bound) (ht : second.length ≤ bound) :
    HeightBound (coin colors width primary left right choice sourceSign source first second).data.decode (2*width) ∧
      (coin colors width primary left right choice sourceSign source first second).work ≤ coinWork width bound := by
  let total := sumFin width (point colors width primary left right choice sourceSign source first second)
  let denominator := ofCounter width
  have hpnt (index : Fin width) := point_bounds colors width primary left right choice sourceSign source first second index
    bound hq hw hp hl hr hs hf ht
  have htotal : HeightBound total.data.decode width := by
    simpa using sumFin_height width 0 _ (fun index => (hpnt index).1)
  have hden : HeightBound denominator.data.decode width := by
    rw [ofCounter_value]; exact HeightBound.nat_coarse width
  have wtotal : total.work ≤ width*(pointWork bound + primitiveWorkBound (width+1)+2)+2 := by
    simpa using sumFin_work width 0 (pointWork bound) _ (fun index => (hpnt index).1) (fun index => (hpnt index).2)
  have wden : denominator.work ≤ 60*(width+1)^2 := ofCounter_work width
  have wresult := quotient_work total.data denominator.data width htotal hden
  constructor
  · change HeightBound (quotient total.data denominator.data).data.decode _
    rw [quotient_value]
    exact (htotal.div hden).mono (by omega)
  · change total.work + denominator.work + (quotient total.data denominator.data).work + 3 ≤ _
    unfold coinWork
    omega

def average (colors width primary left right : ℕ) (sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  let positive := coin colors width primary left right true sourceSign source first second
  let negative := coin colors width primary left right false sourceSign source first second
  let total := RationalBits.add positive.data negative.data
  let result := RationalBits.multiply total.data half
  ⟨result.data, positive.work + negative.work + total.work + result.work + 4⟩

theorem average_value (colors width primary left right : ℕ) (sourceSign : Bool)
    (source first second : List Bool) :
    (average colors width primary left right sourceSign source first second).data.decode =
      LocalMarkedProgram.blurEntry colors width primary (signedValue sourceSign source)
        (value first) (value second) ((left : ℤ)-right) := by
  simp only [average, RationalBits.multiply_value, RationalBits.add_value, coin_value, half_value,
    LocalMarkedProgram.blurEntry]
  ring

def averageHeight (width : ℕ) : ℕ := 4*width+3
def averageWork (width bound : ℕ) : ℕ := 2*coinWork width bound +
  primitiveWorkBound (2*width) + primitiveWorkBound (4*width+2) + 4

theorem average_bounds (colors width primary left right : ℕ) (sourceSign : Bool)
    (source first second : List Bool) (bound : ℕ)
    (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hl : left ≤ bound) (hr : right ≤ bound) (hs : source.length ≤ bound)
    (hf : first.length ≤ bound) (ht : second.length ≤ bound) :
    HeightBound (average colors width primary left right sourceSign source first second).data.decode
      (averageHeight width) ∧
      (average colors width primary left right sourceSign source first second).work ≤ averageWork width bound := by
  let positive := coin colors width primary left right true sourceSign source first second
  let negative := coin colors width primary left right false sourceSign source first second
  let total := RationalBits.add positive.data negative.data
  have hp' := coin_bounds colors width primary left right true sourceSign source first second bound hq hw hp hl hr hs hf ht
  have hn' := coin_bounds colors width primary left right false sourceSign source first second bound hq hw hp hl hr hs hf ht
  have hh : HeightBound half.decode 2 := by rw [half_value]; norm_num [HeightBound]
  have htotal : HeightBound total.data.decode (4*width+1) := by
    rw [RationalBits.add_value]
    exact (hp'.1.add hn'.1).mono (by omega)
  have wtotal : total.work ≤ primitiveWorkBound (2*width) := RationalBits.add_work _ _ _ hp'.1 hn'.1
  have wp : positive.work ≤ coinWork width bound := hp'.2
  have wn : negative.work ≤ coinWork width bound := hn'.2
  have wresult := RationalBits.multiply_work total.data half (4*width+2) (htotal.mono (by omega)) (hh.mono (by omega))
  constructor
  · change HeightBound (RationalBits.multiply total.data half).data.decode _
    rw [RationalBits.multiply_value]
    exact htotal.mul hh
  · change positive.work + negative.work + total.work + (RationalBits.multiply total.data half).work + 4 ≤ _
    unfold averageWork
    omega

end CurrentAFT.BinaryMarkedKernel

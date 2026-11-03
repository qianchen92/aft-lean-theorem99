import AFT.BinaryChartArray
import AFT.UnaryPolynomialCounters
import CurrentAFT.RationalFirstResponseProgram

/-! # Executed anchor-sign functional with sequential input reads -/
namespace CurrentAFT.BinaryRankOneFunctional
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter subtractCounter lessCounter

def anchor (count color : ℕ) : RationalResult :=
  let doubled := addCounter color color
  let last := subtractCounter count 1
  let left := lessCounter doubled.count last.count
  let right := lessCounter last.count doubled.count
  let negative := RationalBits.negate one
  ⟨if left.value then negative.data else if right.value then one else zero,
    doubled.work+last.work+left.work+right.work+negative.work+6⟩

theorem anchor_value (count color : ℕ) :
    (anchor count color).data.decode =
      if 2*color<count-1 then (-1:ℚ) else if count-1<2*color then 1 else 0 := by
  have hl := lessCounter_value (2*color) (count-1)
  have hr := lessCounter_value (count-1) (2*color)
  unfold anchor
  dsimp only
  simp only [addCounter_value, subtractCounter_value, ← two_mul]
  by_cases h : (lessCounter (2*color) (count-1)).value = true
  · simp only [if_pos h, RationalBits.negate_value, one_value, if_pos (hl.mp h)]
  · rw [if_neg h, if_neg (fun hp => h (hl.mpr hp))]
    by_cases h' : (lessCounter (count-1) (2*color)).value = true
    · simp only [if_pos h', one_value, if_pos (hr.mp h')]
    · simp only [if_neg h', zero_value, if_neg (fun hp => h' (hr.mpr hp))]

theorem anchor_height (count color : ℕ) : HeightBound (anchor count color).data.decode 1 := by
  rw [anchor_value]
  split_ifs <;> norm_num [HeightBound]

theorem anchor_work (count : ℕ) (color : Fin count) :
    (anchor count color.val).work ≤ 30*count+primitiveWorkBound 1+20 := by
  have hd := addCounter_work color.val color.val
  have hs := subtractCounter_work_left count 1
  have hl := lessCounter_work (addCounter color.val color.val).count (subtractCounter count 1).count
  have hr := lessCounter_work (subtractCounter count 1).count (addCounter color.val color.val).count
  have hn := RationalBits.negate_work one 1
  simp only [addCounter_value, subtractCounter_value] at hl hr
  change _+_+_+_+_+6 ≤ _
  simp only [addCounter_value, subtractCounter_value]
  omega

def term {count : ℕ} (input : Vector RationalBits count) (color : Fin count) : RationalResult :=
  let coefficient := anchor count color.val
  let value := readVector zero input color
  let result := RationalBits.multiply coefficient.data value.value
  ⟨result.data, coefficient.work+value.work+result.work+3⟩

theorem term_value {count : ℕ} (input : Vector RationalBits count) (color : Fin count) :
    (term input color).data.decode =
      (if 2*color.val<count-1 then (-1:ℚ) else if count-1<2*color.val then 1 else 0)*(input.get color).decode := by
  simp only [term, RationalBits.multiply_value, anchor_value, readVector_value]

def current {count : ℕ} (input : Vector RationalBits count) : RationalResult := sumFin count (term input)

theorem current_value {count : ℕ} (input : Vector RationalBits count) :
    (current input).data.decode =
      ∑ color : Fin count, (if 2*color.val<count-1 then (-1:ℚ) else if count-1<2*color.val then 1 else 0)*(input.get color).decode := by
  simp only [current, sumFin_value, term_value]

def height (count bits : ℕ) := (count+1)*(bits+2)
def work (count bits : ℕ) :=
  count*(33*count+primitiveWorkBound 1+32+primitiveWorkBound (bits+1)+primitiveWorkBound (height count bits))+2

theorem term_height {count : ℕ} (input : Vector RationalBits count) (bits : ℕ)
    (hi : ∀ color, HeightBound (input.get color).decode bits) (color : Fin count) :
    HeightBound (term input color).data.decode (bits+1) := by
  change HeightBound (RationalBits.multiply _ _).data.decode _
  rw [RationalBits.multiply_value, readVector_value]
  exact ((anchor_height count color.val).mul (hi color)).mono (by omega)

theorem term_work {count : ℕ} (input : Vector RationalBits count) (bits : ℕ)
    (hi : ∀ color, HeightBound (input.get color).decode bits) (color : Fin count) :
    (term input color).work ≤ 33*count+primitiveWorkBound 1+30+primitiveWorkBound (bits+1) := by
  have ha := anchor_work count color
  have hr := readVector_work zero input color
  have hm := RationalBits.multiply_work (anchor count color.val).data (readVector zero input color).value (bits+1)
    ((anchor_height count color.val).mono (by omega)) (by rw [readVector_value]; exact (hi color).mono (by omega))
  change _+_+_+3 ≤ _
  omega

theorem current_bounds {count : ℕ} (input : Vector RationalBits count) (bits : ℕ)
    (hi : ∀ color, HeightBound (input.get color).decode bits) :
    HeightBound (current input).data.decode (height count bits) ∧
      (current input).work ≤ work count bits := by
  constructor
  · exact (sumFin_height count (bits+1) (term input) (term_height input bits hi)).mono (by unfold height; nlinarith)
  · exact (sumFin_work count (bits+1) (33*count+primitiveWorkBound 1+30+primitiveWorkBound (bits+1)) (term input)
      (term_height input bits hi) (term_work input bits hi)).trans_eq (by unfold work height; ring)

noncomputable def heightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ := (count+1)*(bits+2)
noncomputable def workPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(33*count+Polynomial.C (primitiveWorkBound 1)+32+primitiveWorkPolynomial (bits+1)+primitiveWorkPolynomial (heightPolynomial count bits))+2

theorem heightPolynomial_eval (count bits : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial count bits).eval security = height (count.eval security) (bits.eval security) := by
  simp only [heightPolynomial, height, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]

theorem workPolynomial_eval (count bits : Polynomial ℕ) (security : ℕ) :
    (workPolynomial count bits).eval security = work (count.eval security) (bits.eval security) := by
  simp only [workPolynomial, work, heightPolynomial_eval, primitiveWorkPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one]

end CurrentAFT.BinaryRankOneFunctional

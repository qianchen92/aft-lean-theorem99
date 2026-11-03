import CurrentAFT.BinaryMassLiftFormula

/-! # Executed binary affine mixture with derived operand heights -/
namespace CurrentAFT.BinaryMixture
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (rate first second : RationalBits) : RationalResult :=
  let negative := RationalBits.negate rate
  let remaining := RationalBits.add one negative.data
  let left := RationalBits.multiply remaining.data first
  let right := RationalBits.multiply rate second
  let result := RationalBits.add left.data right.data
  ⟨result.data,negative.work+remaining.work+left.work+right.work+result.work+5⟩

theorem current_value (rate first second : RationalBits) :
    (current rate first second).data.decode=(1-rate.decode)*first.decode+rate.decode*second.decode := by
  simp only [current,RationalBits.add_value,RationalBits.negate_value,RationalBits.multiply_value,one_value,sub_eq_add_neg]

def height (bits : ℕ) := 4*bits+2
def work (bits : ℕ) := 5*primitiveWorkBound (height bits)+5

theorem current_bounds (rate first second : RationalBits) (bits : ℕ)
    (hr : HeightBound rate.decode bits) (hf : HeightBound first.decode bits) (hs : HeightBound second.decode bits) :
    HeightBound (current rate first second).data.decode (height bits) ∧ (current rate first second).work ≤ work bits := by
  let negative := RationalBits.negate rate
  let remaining := RationalBits.add one negative.data
  let left := RationalBits.multiply remaining.data first
  let right := RationalBits.multiply rate second
  have hn : HeightBound negative.data.decode bits := by rw [RationalBits.negate_value]; exact hr.neg
  have hm : HeightBound remaining.data.decode (bits+1) := by
    rw [RationalBits.add_value,one_value]
    simpa only [zero_add] using HeightBound.one.add hn
  have hl : HeightBound left.data.decode (2*bits+1) := by
    rw [RationalBits.multiply_value]
    convert hm.mul hf using 1; omega
  have ht : HeightBound right.data.decode (2*bits) := by
    rw [RationalBits.multiply_value]
    convert hr.mul hs using 1; omega
  have wn : negative.work ≤ primitiveWorkBound (height bits) := RationalBits.negate_work rate _
  have wm := RationalBits.add_work one negative.data (height bits)
    (by rw [one_value]; exact HeightBound.one.mono (by unfold height; omega)) (hn.mono (by unfold height; omega))
  have wl := RationalBits.multiply_work remaining.data first (height bits) (hm.mono (by unfold height; omega)) (hf.mono (by unfold height; omega))
  have wt := RationalBits.multiply_work rate second (height bits) (hr.mono (by unfold height; omega)) (hs.mono (by unfold height; omega))
  have wa := RationalBits.add_work left.data right.data (height bits) (hl.mono (by unfold height; omega)) (ht.mono (by unfold height; omega))
  constructor
  · change HeightBound (RationalBits.add left.data right.data).data.decode _
    rw [RationalBits.add_value]
    exact (hl.add ht).mono (by unfold height; omega)
  · change negative.work+remaining.work+left.work+right.work+(RationalBits.add left.data right.data).work+5 ≤ _
    unfold work
    dsimp only [negative,remaining,left,right] at wn wm wl wt wa ⊢
    omega

noncomputable def heightPolynomial (bits : Polynomial ℕ) : Polynomial ℕ := 4*bits+2
noncomputable def workPolynomial (bits : Polynomial ℕ) : Polynomial ℕ := 5*primitiveWorkPolynomial (heightPolynomial bits)+5

theorem heightPolynomial_eval (bits : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial bits).eval security=height (bits.eval security) := by
  simp only [heightPolynomial,height,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
theorem workPolynomial_eval (bits : Polynomial ℕ) (security : ℕ) :
    (workPolynomial bits).eval security=work (bits.eval security) := by
  simp only [workPolynomial,work,heightPolynomial_eval,primitiveWorkPolynomial_eval,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]

end CurrentAFT.BinaryMixture

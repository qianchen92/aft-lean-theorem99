import AFT.BinaryPositiveDraw
import AFT.BinarySeriesPolynomials

/-! # Literal polynomial bounds for binary finite sampling -/
namespace AFT.BinaryArithmetic
open Polynomial RationalBits

noncomputable def dyadicFloorWorkPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  1000*(bits+height+2)^2+primitiveWorkPolynomial (bits+height)+6*bits+16
noncomputable def sumDigitsWorkPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(10*(count+1)*(bits+1)+4)+2
noncomputable def ticketTableDigitPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  (count+1)*(bits+height+2)+1
noncomputable def ticketTableWorkPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(dyadicFloorWorkPolynomial height bits+3)+sumDigitsWorkPolynomial count (bits+height+1)+
    2*bits+20*ticketTableDigitPolynomial count height bits+20
noncomputable def binaryRationalDrawPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  ticketTableWorkPolynomial count height bits+3*bits+
    count*(10*ticketTableDigitPolynomial count height bits+5)+2*count+6
noncomputable def sumArrayWorkPolynomial (count height : Polynomial ℕ) : Polynomial ℕ :=
  count*(3*count+3+primitiveWorkPolynomial ((count+1)*(height+1))+2)+2
noncomputable def normalizeArrayWorkPolynomial (count height : Polynomial ℕ) : Polynomial ℕ :=
  sumArrayWorkPolynomial count height+
    count*(3*count+3+2*primitiveWorkPolynomial (height+count*(height+1))+6)+4
noncomputable def binaryPositiveNormalizePolynomial (count height : Polynomial ℕ) : Polynomial ℕ :=
  count*(3*count+9)+sumArrayWorkPolynomial count height+normalizeArrayWorkPolynomial count height+5*count+10
noncomputable def binaryPositiveDrawPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  binaryPositiveNormalizePolynomial count height+2*bits+
    binaryRationalDrawPolynomial count (height+count*(height+1)) (bits+count+1)+4

@[simp] theorem dyadicFloorWorkPolynomial_eval (height bits : Polynomial ℕ) (n : ℕ) :
    (dyadicFloorWorkPolynomial height bits).eval n=dyadicFloorWork (height.eval n) (bits.eval n) := by
  simp only [dyadicFloorWorkPolynomial,dyadicFloorWork,eval_add,eval_mul,eval_pow,eval_ofNat,primitiveWorkPolynomial_eval]
@[simp] theorem sumDigitsWorkPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (sumDigitsWorkPolynomial count bits).eval n=sumDigitsWork (count.eval n) (bits.eval n) := by
  simp only [sumDigitsWorkPolynomial,sumDigitsWork,eval_add,eval_mul,eval_ofNat,eval_one]
@[simp] theorem ticketTableDigitPolynomial_eval (count height bits : Polynomial ℕ) (n : ℕ) :
    (ticketTableDigitPolynomial count height bits).eval n=ticketTableDigitBound (count.eval n) (height.eval n) (bits.eval n) := by
  simp only [ticketTableDigitPolynomial,ticketTableDigitBound,eval_add,eval_mul,eval_ofNat,eval_one]
@[simp] theorem ticketTableWorkPolynomial_eval (count height bits : Polynomial ℕ) (n : ℕ) :
    (ticketTableWorkPolynomial count height bits).eval n=ticketTableWork (count.eval n) (height.eval n) (bits.eval n) := by
  simp only [ticketTableWorkPolynomial,ticketTableWork,eval_add,eval_mul,eval_ofNat,eval_one,
    dyadicFloorWorkPolynomial_eval,sumDigitsWorkPolynomial_eval,ticketTableDigitPolynomial_eval]
@[simp] theorem binaryRationalDrawPolynomial_eval (count height bits : Polynomial ℕ) (n : ℕ) :
    (binaryRationalDrawPolynomial count height bits).eval n=binaryRationalDrawWork (count.eval n) (height.eval n) (bits.eval n) := by
  simp only [binaryRationalDrawPolynomial,binaryRationalDrawWork,eval_add,eval_mul,eval_ofNat,
    ticketTableWorkPolynomial_eval,ticketTableDigitPolynomial_eval]
@[simp] theorem sumArrayWorkPolynomial_eval (count height : Polynomial ℕ) (n : ℕ) :
    (sumArrayWorkPolynomial count height).eval n=sumArrayWork (count.eval n) (height.eval n) := by
  simp only [sumArrayWorkPolynomial,sumArrayWork,eval_add,eval_mul,eval_ofNat,eval_one,primitiveWorkPolynomial_eval]
@[simp] theorem normalizeArrayWorkPolynomial_eval (count height : Polynomial ℕ) (n : ℕ) :
    (normalizeArrayWorkPolynomial count height).eval n=normalizeArrayWork (count.eval n) (height.eval n) := by
  simp only [normalizeArrayWorkPolynomial,normalizeArrayWork,eval_add,eval_mul,eval_ofNat,eval_one,
    sumArrayWorkPolynomial_eval,primitiveWorkPolynomial_eval]
@[simp] theorem binaryPositiveNormalizePolynomial_eval (count height : Polynomial ℕ) (n : ℕ) :
    (binaryPositiveNormalizePolynomial count height).eval n=binaryPositiveNormalizeWork (count.eval n) (height.eval n) := by
  simp only [binaryPositiveNormalizePolynomial,binaryPositiveNormalizeWork,eval_add,eval_mul,eval_ofNat,
    sumArrayWorkPolynomial_eval,normalizeArrayWorkPolynomial_eval]
@[simp] theorem binaryPositiveDrawPolynomial_eval (count height bits : Polynomial ℕ) (n : ℕ) :
    (binaryPositiveDrawPolynomial count height bits).eval n=binaryPositiveDrawWork (count.eval n) (height.eval n) (bits.eval n) := by
  simp only [binaryPositiveDrawPolynomial,binaryPositiveDrawWork,eval_add,eval_mul,eval_ofNat,eval_one,
    binaryPositiveNormalizePolynomial_eval,binaryRationalDrawPolynomial_eval]

theorem normalizeArrayWork_mono {c d h k : ℕ} (hc : c≤ d) (hh : h≤ k) :
    normalizeArrayWork c h≤ normalizeArrayWork d k := by
  unfold normalizeArrayWork sumArrayWork primitiveWorkBound
  gcongr

theorem ticketTableWork_mono {c d h k b e : ℕ} (hc : c≤ d) (hh : h≤ k) (hb : b≤ e) :
    ticketTableWork c h b≤ ticketTableWork d k e := by
  unfold ticketTableWork ticketTableDigitBound dyadicFloorWork sumDigitsWork primitiveWorkBound
  gcongr

theorem binaryRationalDrawWork_mono {c d h k b e : ℕ} (hc : c≤ d) (hh : h≤ k) (hb : b≤ e) :
    binaryRationalDrawWork c h b≤ binaryRationalDrawWork d k e := by
  unfold binaryRationalDrawWork ticketTableWork ticketTableDigitBound dyadicFloorWork sumDigitsWork primitiveWorkBound
  gcongr

theorem binaryPositiveDrawWork_mono {c d h k b e : ℕ} (hc : c≤ d) (hh : h≤ k) (hb : b≤ e) :
    binaryPositiveDrawWork c h b≤ binaryPositiveDrawWork d k e := by
  unfold binaryPositiveDrawWork binaryPositiveNormalizeWork normalizeArrayWork sumArrayWork
    binaryRationalDrawWork ticketTableWork ticketTableDigitBound dyadicFloorWork sumDigitsWork primitiveWorkBound
  gcongr

end AFT.BinaryArithmetic

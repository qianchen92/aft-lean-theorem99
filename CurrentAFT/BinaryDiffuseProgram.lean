import CurrentAFT.BinaryTrimmedPair
import CurrentAFT.CurrentGaussianBits
import CurrentAFT.LocalDiffuseProgram
import AFT.BinaryPublicBaseline

/-! # The diffuse local leaf evaluated on actual binary data

The Gaussian table is materialized once. Every access scans its stored
list, and the two-dimensional average uses actual binary rational sums.
The protected scalar and the two output colors remain retained inputs.
-/
namespace CurrentAFT.BinaryDiffuseProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open AFT.FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def coin (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  let baseline := binaryBaselineStart colors width primary (!choice)
  let leftCode := canonicalCounter left
  let rightCode := canonicalCounter right
  let blur := signedAdd false true leftCode.digits rightCode.digits
  let start := signedAdd baseline.negative blur.negative baseline.digits blur.digits
  let colorCode := canonicalCounter colors
  let widthCode := canonicalCounter width
  let result := BinaryTrimmedPair.pair start.negative sourceSign colorCode.digits widthCode.digits
    start.digits source first second
  ⟨result.data, baseline.work + leftCode.work + rightCode.work + blur.work + start.work +
    colorCode.work + widthCode.work + result.work + 8⟩

attribute [local irreducible] binaryBaselineStart canonicalCounter signedAdd BinaryTrimmedPair.pair coin

theorem baseline_value (colors width primary : ℕ) (choice : Bool) :
    signedValue (binaryBaselineStart colors width primary (!choice)).negative
      (binaryBaselineStart colors width primary (!choice)).digits =
      if LocalDiffuseProgram.direction colors primary choice then (width : ℤ) else -2*(width : ℤ)+1 := by
  rw [binaryBaselineStart_value]
  by_cases hl : 2*primary < colors-1
  · simp only [V7Calibration.publicAnchorStartProgram, LocalDiffuseProgram.direction, if_pos hl,
      Bool.false_eq_true, if_false]
    ring
  · by_cases hu : colors-1 < 2*primary
    · simp only [V7Calibration.publicAnchorStartProgram, LocalDiffuseProgram.direction, if_neg hl, if_pos hu, if_true]
      ring
    · cases choice <;> simp only [V7Calibration.publicAnchorStartProgram, LocalDiffuseProgram.direction,
        if_neg hl, if_neg hu, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] <;> ring

theorem coin_value (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) :
    (coin colors width primary left right choice sourceSign source first second).data.decode =
      LocalDiffuseProgram.coinEntry colors width primary (signedValue sourceSign source)
        ((left : ℤ)-right) choice (value first) (value second) := by
  unfold coin
  rw [BinaryTrimmedPair.pair_value, signedAdd_value, baseline_value, signedAdd_value]
  simp only [signedValue, Bool.false_eq_true, if_false, if_true, canonicalCounter_value]
  unfold LocalDiffuseProgram.coinEntry
  rfl

def coinIntegerBound (bound : ℕ) : ℕ := 4*bound+10
def coinWork (bound : ℕ) : ℕ :=
  1000*(3*bound+2)^2 + 4*(50*(bound+1)^2) +
    (20*bound+8) + (20*(2*bound+2)+8) + BinaryTrimmedPair.pairWork (coinIntegerBound bound) + 8

theorem coin_bounds (colors width primary left right : ℕ) (choice sourceSign : Bool)
    (source first second : List Bool) (bound : ℕ)
    (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hl : left ≤ bound) (hr : right ≤ bound)
    (hsource : source.length ≤ bound) (hfirst : first.length ≤ bound) (hsecond : second.length ≤ bound) :
    HeightBound (coin colors width primary left right choice sourceSign source first second).data.decode
      (2*coinIntegerBound bound+8) ∧
    (coin colors width primary left right choice sourceSign source first second).work ≤ coinWork bound := by
  let baseline := binaryBaselineStart colors width primary (!choice)
  let leftCode := canonicalCounter left
  let rightCode := canonicalCounter right
  let blur := signedAdd false true leftCode.digits rightCode.digits
  let start := signedAdd baseline.negative blur.negative baseline.digits blur.digits
  let colorCode := canonicalCounter colors
  let widthCode := canonicalCounter width
  have size_le (number : ℕ) : number.size ≤ number := Nat.size_le.mpr (Nat.lt_two_pow_self (n := number))
  have hleft : leftCode.digits.length ≤ bound := by rw [canonicalCounter_length]; exact (size_le _).trans hl
  have hright : rightCode.digits.length ≤ bound := by rw [canonicalCounter_length]; exact (size_le _).trans hr
  have hcolor : colorCode.digits.length ≤ bound := by rw [canonicalCounter_length]; exact (size_le _).trans hq
  have hwidth : widthCode.digits.length ≤ bound := by rw [canonicalCounter_length]; exact (size_le _).trans hw
  have hbase : baseline.digits.length ≤ 2*bound+2 :=
    (binaryBaselineStart_length _ _ _ _).trans (by omega)
  have hblur : blur.digits.length ≤ bound+1 := (signedAdd_length _ _ _ _).trans (by omega)
  have hstart : start.digits.length ≤ 2*bound+3 := (signedAdd_length _ _ _ _).trans (by omega)
  have hbound : 1 ≤ coinIntegerBound bound := by unfold coinIntegerBound; omega
  have hq' : colorCode.digits.length ≤ coinIntegerBound bound := by unfold coinIntegerBound; omega
  have hw' : widthCode.digits.length ≤ coinIntegerBound bound := by unfold coinIntegerBound; omega
  have hf' : first.length ≤ coinIntegerBound bound := by unfold coinIntegerBound; omega
  have hs' : second.length ≤ coinIntegerBound bound := by unfold coinIntegerBound; omega
  have hh := BinaryTrimmedPair.pair_height start.negative sourceSign colorCode.digits widthCode.digits
    start.digits source first second (coinIntegerBound bound) hbound hq' hw' hf' hs'
  have wp := BinaryTrimmedPair.pair_work start.negative sourceSign colorCode.digits widthCode.digits
    start.digits source first second (coinIntegerBound bound) hbound hq' hw'
    (by unfold coinIntegerBound; omega) (by unfold coinIntegerBound; omega) hf' hs'
  have wb : baseline.work ≤ 1000*(3*bound+2)^2 :=
    (binaryBaselineStart_work colors width primary (!choice)).trans
      (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (by omega) 2))
  have wl : leftCode.work ≤ 50*(bound+1)^2 :=
    (canonicalCounter_work left).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have wr : rightCode.work ≤ 50*(bound+1)^2 :=
    (canonicalCounter_work right).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have wc : colorCode.work ≤ 50*(bound+1)^2 :=
    (canonicalCounter_work colors).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have ww : widthCode.work ≤ 50*(bound+1)^2 :=
    (canonicalCounter_work width).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have wblur : blur.work ≤ 20*bound+8 := (signedAdd_work _ _ _ _).trans (by omega)
  have wstart : start.work ≤ 20*(2*bound+2)+8 := (signedAdd_work _ _ _ _).trans (by omega)
  constructor
  · unfold coin
    exact hh
  · unfold coin
    change baseline.work + leftCode.work + rightCode.work + blur.work + start.work +
      colorCode.work + widthCode.work +
      (BinaryTrimmedPair.pair start.negative sourceSign colorCode.digits widthCode.digits
        start.digits source first second).work + 8 ≤ _
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
      LocalDiffuseProgram.blurEntry colors width primary (signedValue sourceSign source)
        (value first) (value second) ((left : ℤ)-right) := by
  simp only [average, RationalBits.multiply_value, RationalBits.add_value, coin_value, half_value,
    LocalDiffuseProgram.blurEntry]
  ring

def averageHeight (bound : ℕ) : ℕ := 2*(2*coinIntegerBound bound+8)+3
def averageWork (bound : ℕ) : ℕ := 2*coinWork bound +
  primitiveWorkBound (2*coinIntegerBound bound+8) +
  primitiveWorkBound (2*(2*coinIntegerBound bound+8)+2) + 4

theorem average_bounds (colors width primary left right : ℕ) (sourceSign : Bool)
    (source first second : List Bool) (bound : ℕ)
    (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hl : left ≤ bound) (hr : right ≤ bound)
    (hsource : source.length ≤ bound) (hfirst : first.length ≤ bound) (hsecond : second.length ≤ bound) :
    HeightBound (average colors width primary left right sourceSign source first second).data.decode
      (averageHeight bound) ∧
    (average colors width primary left right sourceSign source first second).work ≤ averageWork bound := by
  let positive := coin colors width primary left right true sourceSign source first second
  let negative := coin colors width primary left right false sourceSign source first second
  let total := RationalBits.add positive.data negative.data
  have hpos := coin_bounds colors width primary left right true sourceSign source first second bound
    hq hw hp hl hr hsource hfirst hsecond
  have hneg := coin_bounds colors width primary left right false sourceSign source first second bound
    hq hw hp hl hr hsource hfirst hsecond
  have hh : HeightBound half.decode 2 := by rw [half_value]; norm_num [HeightBound]
  have htotal : HeightBound total.data.decode (2*(2*coinIntegerBound bound+8)+1) := by
    rw [RationalBits.add_value]
    exact (hpos.1.add hneg.1).mono (by omega)
  have wtotal : total.work ≤ primitiveWorkBound (2*coinIntegerBound bound+8) :=
    RationalBits.add_work positive.data negative.data (2*coinIntegerBound bound+8) hpos.1 hneg.1
  have wresult := RationalBits.multiply_work total.data half (2*(2*coinIntegerBound bound+8)+2)
    (htotal.mono (by omega)) (hh.mono (by omega))
  constructor
  · change HeightBound (RationalBits.multiply total.data half).data.decode _
    rw [RationalBits.multiply_value]
    exact (htotal.mul hh).mono (by unfold averageHeight; omega)
  · change positive.work + negative.work + total.work + (RationalBits.multiply total.data half).work + 4 ≤ _
    have wp : positive.work ≤ coinWork bound := hpos.2
    have wn : negative.work ≤ coinWork bound := hneg.2
    unfold averageWork
    omega

def term (colors width primary cutoff : ℕ) (weights : Vector RationalBits (2*cutoff+1))
    (sourceSign : Bool) (source first second : List Bool)
    (left right : Fin (2*cutoff+1)) : RationalResult :=
  let firstWeight := readVector zero weights left
  let secondWeight := readVector zero weights right
  let response := average colors width primary left.val right.val sourceSign source first second
  let probability := RationalBits.multiply firstWeight.value secondWeight.value
  let result := RationalBits.multiply probability.data response.data
  ⟨result.data, firstWeight.work + secondWeight.work + response.work + probability.work + result.work + 5⟩

theorem term_value (colors width primary cutoff : ℕ) (weights : Vector RationalBits (2*cutoff+1))
    (sourceSign : Bool) (source first second : List Bool) (left right : Fin (2*cutoff+1)) :
    (term colors width primary cutoff weights sourceSign source first second left right).data.decode =
      (weights.get left).decode*(weights.get right).decode*
        LocalDiffuseProgram.blurEntry colors width primary (signedValue sourceSign source)
          (value first) (value second) ((left.val : ℤ)-right.val) := by
  simp only [term, RationalBits.multiply_value, readVector_value, average_value]

def termHeight (bound gaussianHeight : ℕ) : ℕ := 2*gaussianHeight + averageHeight bound
def termWork (count bound gaussianHeight : ℕ) : ℕ :=
  2*(3*count+3) + averageWork bound + 2*primitiveWorkBound (termHeight bound gaussianHeight) + 5

theorem term_bounds (colors width primary cutoff : ℕ) (weights : Vector RationalBits (2*cutoff+1))
    (sourceSign : Bool) (source first second : List Bool) (left right : Fin (2*cutoff+1))
    (bound gaussianHeight : ℕ) (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hcutoff : 2*cutoff ≤ bound) (hsource : source.length ≤ bound)
    (hfirst : first.length ≤ bound) (hsecond : second.length ≤ bound)
    (hweights : ∀ index, HeightBound (weights.get index).decode gaussianHeight) :
    HeightBound (term colors width primary cutoff weights sourceSign source first second left right).data.decode
      (termHeight bound gaussianHeight) ∧
    (term colors width primary cutoff weights sourceSign source first second left right).work ≤
      termWork (2*cutoff+1) bound gaussianHeight := by
  let firstWeight := readVector zero weights left
  let secondWeight := readVector zero weights right
  let response := average colors width primary left.val right.val sourceSign source first second
  let probability := RationalBits.multiply firstWeight.value secondWeight.value
  have hl : left.val ≤ bound := by have := left.isLt; omega
  have hr : right.val ≤ bound := by have := right.isLt; omega
  have hav := average_bounds colors width primary left.val right.val sourceSign source first second bound
    hq hw hp hl hr hsource hfirst hsecond
  have hfw : HeightBound firstWeight.value.decode gaussianHeight := by
    rw [readVector_value]; exact hweights left
  have hsw : HeightBound secondWeight.value.decode gaussianHeight := by
    rw [readVector_value]; exact hweights right
  have hprob : HeightBound probability.data.decode (2*gaussianHeight) := by
    rw [RationalBits.multiply_value]
    exact (hfw.mul hsw).mono (by omega)
  have wfw : firstWeight.work ≤ 3*(2*cutoff+1)+3 := readVector_work zero weights left
  have wsw : secondWeight.work ≤ 3*(2*cutoff+1)+3 := readVector_work zero weights right
  have wr : response.work ≤ averageWork bound := hav.2
  have wp : probability.work ≤ primitiveWorkBound (termHeight bound gaussianHeight) :=
    RationalBits.multiply_work firstWeight.value secondWeight.value _
      (hfw.mono (by unfold termHeight; omega)) (hsw.mono (by unfold termHeight; omega))
  have wresult := RationalBits.multiply_work probability.data response.data (termHeight bound gaussianHeight)
    (hprob.mono (by unfold termHeight; omega)) (hav.1.mono (by unfold termHeight; omega))
  constructor
  · change HeightBound (RationalBits.multiply probability.data response.data).data.decode _
    rw [RationalBits.multiply_value]
    exact hprob.mul hav.1
  · change firstWeight.work + secondWeight.work + response.work + probability.work +
      (RationalBits.multiply probability.data response.data).work + 5 ≤ _
    unfold termWork
    omega

def sum (colors width primary cutoff : ℕ) (weights : Vector RationalBits (2*cutoff+1))
    (sourceSign : Bool) (source first second : List Bool) : RationalResult :=
  sumFin (2*cutoff+1) (fun left => sumFin (2*cutoff+1)
    (fun right => term colors width primary cutoff weights sourceSign source first second left right))

def sumHeight (count bound gaussianHeight : ℕ) : ℕ :=
  count*(count*(termHeight bound gaussianHeight+1)+1)
def sumWork (count bound gaussianHeight : ℕ) : ℕ :=
  count*(count*(termWork count bound gaussianHeight +
    primitiveWorkBound ((count+1)*(termHeight bound gaussianHeight+1))+2)+2 +
    primitiveWorkBound ((count+1)*(count*(termHeight bound gaussianHeight+1)+1))+2)+2

theorem sum_bounds (colors width primary cutoff : ℕ) (weights : Vector RationalBits (2*cutoff+1))
    (sourceSign : Bool) (source first second : List Bool) (bound gaussianHeight : ℕ)
    (hq : colors ≤ bound) (hw : width ≤ bound) (hp : primary ≤ bound)
    (hcutoff : 2*cutoff ≤ bound) (hsource : source.length ≤ bound)
    (hfirst : first.length ≤ bound) (hsecond : second.length ≤ bound)
    (hweights : ∀ index, HeightBound (weights.get index).decode gaussianHeight) :
    HeightBound (sum colors width primary cutoff weights sourceSign source first second).data.decode
      (sumHeight (2*cutoff+1) bound gaussianHeight) ∧
    (sum colors width primary cutoff weights sourceSign source first second).work ≤
      sumWork (2*cutoff+1) bound gaussianHeight := by
  have ht (left right : Fin (2*cutoff+1)) := term_bounds colors width primary cutoff weights sourceSign
    source first second left right bound gaussianHeight hq hw hp hcutoff hsource hfirst hsecond hweights
  have hi (left : Fin (2*cutoff+1)) := sumFin_height (2*cutoff+1) (termHeight bound gaussianHeight)
    (fun right => term colors width primary cutoff weights sourceSign source first second left right)
    (fun right => (ht left right).1)
  have wi (left : Fin (2*cutoff+1)) := sumFin_work (2*cutoff+1) (termHeight bound gaussianHeight)
    (termWork (2*cutoff+1) bound gaussianHeight)
    (fun right => term colors width primary cutoff weights sourceSign source first second left right)
    (fun right => (ht left right).1) (fun right => (ht left right).2)
  constructor
  · exact sumFin_height _ _ _ hi
  · exact sumFin_work _ _ _ _ hi wi

def evaluate (security colors width cutoff bits primary : ℕ) (sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  let weights := CurrentGaussianBits.table security cutoff bits
  let result := sum colors width primary cutoff weights.data sourceSign source first second
  ⟨result.data, weights.work + result.work + 2⟩

theorem evaluate_value (security colors width cutoff bits primary : ℕ) (sourceSign : Bool)
    (source first second : List Bool) :
    (evaluate security colors width cutoff bits primary sourceSign source first second).data.decode =
      LocalDiffuseProgram.evaluate security colors width cutoff bits primary (signedValue sourceSign source)
        (value first) (value second) := by
  simp only [evaluate, sum, sumFin_value, term_value, CurrentGaussianBits.table_value,
    windowGaussianWeights, LocalDiffuseProgram.evaluate]
  rw [← (windowIndexEquiv cutoff).sum_comp]
  apply Finset.sum_congr rfl
  intro left _
  rw [← (windowIndexEquiv cutoff).sum_comp]
  apply Finset.sum_congr rfl
  intro right _
  simp only [windowIndexEquiv, Equiv.coe_fn_mk]
  congr 2
  omega

def inputBound (colors width primary cutoff : ℕ) (source first second : List Bool) : ℕ :=
  colors + width + primary + 2*cutoff + source.length + first.length + second.length + 1
def gaussianHeight (security bits : ℕ) : ℕ := 500000000*(CurrentGaussianBits.budget security bits)^6
def evaluateWork (security cutoff bits bound : ℕ) : ℕ :=
  CurrentGaussianBits.tableWork security bits + sumWork (2*cutoff+1) bound (gaussianHeight security bits) + 2

theorem evaluate_bounds (security colors width cutoff bits primary : ℕ) (sourceSign : Bool)
    (source first second : List Bool) (hcutoff : cutoff ≤ (security+2)^2) :
    HeightBound (evaluate security colors width cutoff bits primary sourceSign source first second).data.decode
      (sumHeight (2*cutoff+1) (inputBound colors width primary cutoff source first second)
        (gaussianHeight security bits)) ∧
    (evaluate security colors width cutoff bits primary sourceSign source first second).work ≤
      evaluateWork security cutoff bits (inputBound colors width primary cutoff source first second) := by
  let bound := inputBound colors width primary cutoff source first second
  have hq : colors ≤ bound := by unfold bound inputBound; omega
  have hw : width ≤ bound := by unfold bound inputBound; omega
  have hp : primary ≤ bound := by unfold bound inputBound; omega
  have hc : 2*cutoff ≤ bound := by unfold bound inputBound; omega
  have hs : source.length ≤ bound := by unfold bound inputBound; omega
  have hf : first.length ≤ bound := by unfold bound inputBound; omega
  have ht : second.length ≤ bound := by unfold bound inputBound; omega
  have hsum := sum_bounds colors width primary cutoff (CurrentGaussianBits.table security cutoff bits).data
    sourceSign source first second bound (gaussianHeight security bits) hq hw hp hc hs hf ht
    (CurrentGaussianBits.table_height security cutoff bits hcutoff)
  constructor
  · exact hsum.1
  · have htable := CurrentGaussianBits.table_work security cutoff bits hcutoff
    unfold evaluate evaluateWork
    dsimp only
    exact Nat.add_le_add_right (Nat.add_le_add htable hsum.2) 2

theorem sumWork_mono {count count' bound bound' height height' : ℕ}
    (hc : count ≤ count') (hb : bound ≤ bound') (hh : height ≤ height') :
    sumWork count bound height ≤ sumWork count' bound' height' := by
  unfold sumWork termWork termHeight averageWork averageHeight coinWork coinIntegerBound
    BinaryTrimmedPair.pairWork binarySliceProbabilityWork binaryEndpointProbabilityWork
    binaryIntervalProbabilityWork primitiveWorkBound
  gcongr

theorem evaluateWork_mono {security bits cutoff cutoff' bound bound' : ℕ}
    (hc : cutoff ≤ cutoff') (hb : bound ≤ bound') :
    evaluateWork security cutoff bits bound ≤ evaluateWork security cutoff' bits bound' := by
  unfold evaluateWork
  exact Nat.add_le_add_right (Nat.add_le_add le_rfl (sumWork_mono (by omega) hb le_rfl)) 2

noncomputable def coinIntegerPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := 4*bound+10
noncomputable def averageHeightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  2*(2*coinIntegerPolynomial bound+8)+3
noncomputable def coinWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  1000*(3*bound+2)^2 + 4*(50*(bound+1)^2) +
    (20*bound+8) + (20*(2*bound+2)+8) + BinaryTrimmedPair.pairWorkPolynomial (coinIntegerPolynomial bound) + 8
noncomputable def averageWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  2*coinWorkPolynomial bound + primitiveWorkPolynomial (2*coinIntegerPolynomial bound+8) +
    primitiveWorkPolynomial (2*(2*coinIntegerPolynomial bound+8)+2) + 4
noncomputable def termHeightPolynomial (bound gaussianHeight : Polynomial ℕ) : Polynomial ℕ :=
  2*gaussianHeight + averageHeightPolynomial bound
noncomputable def termWorkPolynomial (count bound gaussianHeight : Polynomial ℕ) : Polynomial ℕ :=
  2*(3*count+3) + averageWorkPolynomial bound +
    2*primitiveWorkPolynomial (termHeightPolynomial bound gaussianHeight) + 5
noncomputable def sumWorkPolynomial (count bound gaussianHeight : Polynomial ℕ) : Polynomial ℕ :=
  count*(count*(termWorkPolynomial count bound gaussianHeight +
    primitiveWorkPolynomial ((count+1)*(termHeightPolynomial bound gaussianHeight+1))+2)+2 +
    primitiveWorkPolynomial ((count+1)*(count*(termHeightPolynomial bound gaussianHeight+1)+1))+2)+2
noncomputable def evaluateWorkPolynomial (cutoff precision bound : Polynomial ℕ) : Polynomial ℕ :=
  CurrentGaussianBits.workPolynomial precision +
    sumWorkPolynomial (2*cutoff+1) bound (500000000*((Polynomial.X+2)^2+precision+2)^6) + 2

theorem evaluateWorkPolynomial_eval (cutoff precision bound : Polynomial ℕ) (security : ℕ) :
    (evaluateWorkPolynomial cutoff precision bound).eval security =
      evaluateWork security (cutoff.eval security) (precision.eval security) (bound.eval security) := by
  simp only [evaluateWorkPolynomial, sumWorkPolynomial, termWorkPolynomial, termHeightPolynomial,
    averageWorkPolynomial, averageHeightPolynomial, coinWorkPolynomial, coinIntegerPolynomial,
    evaluateWork, sumWork, termWork, termHeight, averageWork, averageHeight, coinWork,
    coinIntegerBound, gaussianHeight, CurrentGaussianBits.budget,
    CurrentGaussianBits.workPolynomial_eval, BinaryTrimmedPair.pairWorkPolynomial_eval,
    primitiveWorkPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]

theorem evaluate_polynomial_work (security colors width cutoff primary : ℕ) (sourceSign : Bool)
    (source first second : List Bool) (cutoffBudget precision bound : Polynomial ℕ)
    (hcutoff : cutoff ≤ (security+2)^2) (hc : cutoff ≤ cutoffBudget.eval security)
    (hb : inputBound colors width primary cutoff source first second ≤ bound.eval security) :
    (evaluate security colors width cutoff (precision.eval security) primary sourceSign source first second).work ≤
      (evaluateWorkPolynomial cutoffBudget precision bound).eval security := by
  rw [evaluateWorkPolynomial_eval]
  exact (evaluate_bounds security colors width cutoff (precision.eval security) primary sourceSign
    source first second hcutoff).2.trans (evaluateWork_mono hc hb)

end CurrentAFT.BinaryDiffuseProgram

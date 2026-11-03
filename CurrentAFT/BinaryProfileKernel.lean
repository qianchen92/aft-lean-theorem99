import CurrentAFT.BinaryAnchorProgram
import CurrentAFT.RationalFirstResponseProgram
import AFT.BinaryAveragedSlice

/-! # The current diffuse marginal kernel on actual binary operands -/
namespace CurrentAFT.BinaryProfileKernel
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter signedAdd doubleCounter

def start (width : ℕ) (positive : Bool) : SignedResult :=
  let positiveCode := canonicalCounter width
  let doubled := doubleCounter width
  let negativeCode := canonicalCounter doubled.count
  let negative := signedAdd true false negativeCode.digits [true]
  ⟨if positive then false else negative.negative, if positive then positiveCode.digits else negative.digits,
    positiveCode.work + doubled.work + negativeCode.work + negative.work + 5⟩

theorem start_value (width : ℕ) (positive : Bool) :
    signedValue (start width positive).negative (start width positive).digits =
      if positive then (width:ℤ) else -2*(width:ℤ)+1 := by
  cases positive with
  | false =>
    unfold start
    simp only [Bool.false_eq_true, if_false]
    rw [signedAdd_value]
    simp only [signedValue, if_true, canonicalCounter_value, doubleCounter_value]
    norm_num [value]
  | true => simp only [start, if_true, signedValue, Bool.false_eq_true, if_false, canonicalCounter_value]

def startWork (bound : ℕ) : ℕ :=
  50*(bound+1)^2 + 3*bound+1 + 50*(2*bound+1)^2 + 20*(2*bound+1)+8 + 5

theorem start_bounds (width bound : ℕ) (positive : Bool) (hw : width ≤ bound) :
    (start width positive).digits.length ≤ 2*bound+2 ∧ (start width positive).work ≤ startWork bound := by
  have hp : (canonicalCounter width).digits.length ≤ bound := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := width))).trans hw
  have hn : (canonicalCounter (doubleCounter width).count).digits.length ≤ 2*bound := by
    rw [canonicalCounter_length, doubleCounter_value]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := 2*width))).trans (by omega)
  have hl := signedAdd_length true false (canonicalCounter (doubleCounter width).count).digits [true]
  have hs := signedAdd_work true false (canonicalCounter (doubleCounter width).count).digits [true]
  have wp : (canonicalCounter width).work ≤ 50*(bound+1)^2 :=
    (canonicalCounter_work width).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  have wn : (canonicalCounter (doubleCounter width).count).work ≤ 50*(2*bound+1)^2 :=
    (canonicalCounter_work _).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by rw [doubleCounter_value]; omega) 2))
  simp only [List.length_cons, List.length_nil] at hl hs
  constructor
  · cases positive <;> (simp only [start, Bool.false_eq_true, if_false, if_true]; omega)
  · unfold start startWork
    simp only [doubleCounter_work]
    omega

def current (colors width edgeCutoff scalarCutoff : ℕ) (positive : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : RationalResult :=
  let baseline := start width positive
  let blur := BinaryAnchorProgram.coordinate right.val left.val
  let source := BinaryAnchorProgram.coordinate scalarCutoff scalar.val
  let shifted := signedAdd baseline.negative blur.negative baseline.digits blur.digits
  let colorCode := canonicalCounter colors
  let result := binaryAveragedSlice false false shifted.negative source.negative false
    colorCode.digits [true] shifted.digits source.digits output width
  ⟨result.data, baseline.work + blur.work + source.work + shifted.work + colorCode.work + result.work + 6⟩

theorem current_value (colors width edgeCutoff scalarCutoff : ℕ) (positive : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) :
    (current colors width edgeCutoff scalarCutoff positive output left right scalar).data.decode =
      RationalFirstResponseProgram.profileKernel colors width positive ((left.val:ℤ)-right.val)
        ((scalar.val:ℤ)-scalarCutoff) (value output) := by
  unfold current
  rw [binaryAveragedSlice_value, signedAdd_value, start_value, BinaryAnchorProgram.coordinate_value,
    BinaryAnchorProgram.coordinate_value]
  simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value]
  norm_num [value]
  rfl

def integerBound (bound : ℕ) : ℕ := 8*bound+20
def currentHeight (bound : ℕ) : ℕ := integerBound bound*(2*integerBound bound+7)
def currentWork (bound : ℕ) : ℕ := startWork bound + BinaryAnchorProgram.coordinateWork (2*bound) +
  BinaryAnchorProgram.coordinateWork bound + (20*(4*bound+2)+8) + 50*(bound+1)^2 +
    binaryAveragedSliceWork (integerBound bound) + 6

theorem current_bounds (colors width edgeCutoff scalarCutoff : ℕ) (positive : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) (bound : ℕ)
    (hq : colors ≤ bound) (hw : width ≤ bound) (he : edgeCutoff ≤ bound)
    (hs : scalarCutoff ≤ bound) (ho : output.length ≤ bound) :
    HeightBound (current colors width edgeCutoff scalarCutoff positive output left right scalar).data.decode (currentHeight bound) ∧
      (current colors width edgeCutoff scalarCutoff positive output left right scalar).work ≤ currentWork bound := by
  let baseline := start width positive
  let blur := BinaryAnchorProgram.coordinate right.val left.val
  let source := BinaryAnchorProgram.coordinate scalarCutoff scalar.val
  let shifted := signedAdd baseline.negative blur.negative baseline.digits blur.digits
  let colorCode := canonicalCounter colors
  have hb := start_bounds width bound positive hw
  have hl : left.val ≤ 2*bound := by have := left.isLt; omega
  have hr : right.val ≤ 2*bound := by have := right.isLt; omega
  have hi : scalar.val ≤ 2*bound := by have := scalar.isLt; omega
  have hblur := BinaryAnchorProgram.coordinate_bounds right.val left.val (2*bound) hr (by omega)
  have hsource := BinaryAnchorProgram.coordinate_bounds scalarCutoff scalar.val bound hs hi
  have hbase : baseline.digits.length ≤ 2*bound+2 := hb.1
  have hblur' : blur.digits.length ≤ 4*bound+1 := hblur.1.trans (by omega)
  have hsource' : source.digits.length ≤ 2*bound+1 := hsource.1
  have hshift : shifted.digits.length ≤ 4*bound+3 := (signedAdd_length _ _ _ _).trans (by omega)
  have hcolor : colorCode.digits.length ≤ bound := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := colors))).trans hq
  have hq' : colorCode.digits.length ≤ integerBound bound := by unfold integerBound; omega
  have ht' : shifted.digits.length ≤ integerBound bound := by unfold integerBound; omega
  have hs' : source.digits.length ≤ integerBound bound := by unfold integerBound; omega
  have hw' : width ≤ integerBound bound := by unfold integerBound; omega
  have hboundary : [true].length ≤ integerBound bound := by unfold integerBound; simp
  have hp := binaryAveragedSlice_height false false shifted.negative source.negative false colorCode.digits
    [true] shifted.digits source.digits output width (integerBound bound) hq' hboundary ht' hs' hw'
  have wp := binaryAveragedSlice_work false false shifted.negative source.negative false colorCode.digits
    [true] shifted.digits source.digits output width (integerBound bound) hq' hboundary ht' hs'
    (by unfold integerBound; omega) hw'
  have wb : baseline.work ≤ startWork bound := hb.2
  have wl : blur.work ≤ BinaryAnchorProgram.coordinateWork (2*bound) := hblur.2
  have ws : source.work ≤ BinaryAnchorProgram.coordinateWork bound := hsource.2
  have wshift : shifted.work ≤ 20*(4*bound+2)+8 := (signedAdd_work _ _ _ _).trans (by omega)
  have wc : colorCode.work ≤ 50*(bound+1)^2 :=
    (canonicalCounter_work colors).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by omega) 2))
  constructor
  · exact hp
  · change baseline.work + blur.work + source.work + shifted.work + colorCode.work +
      (binaryAveragedSlice false false shifted.negative source.negative false colorCode.digits
        [true] shifted.digits source.digits output width).work + 6 ≤ _
    unfold currentWork
    omega

noncomputable def integerPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := 8*bound+20
noncomputable def heightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  integerPolynomial bound*(2*integerPolynomial bound+7)
noncomputable def startWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  50*(bound+1)^2 + 3*bound+1 + 50*(2*bound+1)^2 + 20*(2*bound+1)+8+5
noncomputable def sliceWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  100*(bits+2)+20*(bits+2)+11+200*(bits+5)+primitiveWorkPolynomial (bits+3)
noncomputable def anchorWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  110*(bits+1)^2+40*(bits+1)+16+sliceWorkPolynomial (bits+2)+
    primitiveWorkPolynomial bits+primitiveWorkPolynomial (2*bits+6)+8
noncomputable def averagedWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  bits*(anchorWorkPolynomial bits+primitiveWorkPolynomial ((bits+1)*(2*bits+7))+2)+2
noncomputable def workPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  startWorkPolynomial bound+BinaryAnchorProgram.coordinateWorkPolynomial (2*bound)+
    BinaryAnchorProgram.coordinateWorkPolynomial bound+(20*(4*bound+2)+8)+50*(bound+1)^2+
      averagedWorkPolynomial (integerPolynomial bound)+6

theorem heightPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial bound).eval security = currentHeight (bound.eval security) := by
  simp only [heightPolynomial, integerPolynomial, currentHeight, integerBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat]

theorem workPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (workPolynomial bound).eval security = currentWork (bound.eval security) := by
  simp only [workPolynomial, startWorkPolynomial, averagedWorkPolynomial, anchorWorkPolynomial,
    sliceWorkPolynomial, integerPolynomial, currentWork, startWork, integerBound,
    BinaryAnchorProgram.coordinateWorkPolynomial, BinaryAnchorProgram.coordinateWork,
    binaryAveragedSliceWork, binaryAnchorSliceTermWork, binarySliceProbabilityWork,
    binaryEndpointProbabilityWork, binaryIntervalProbabilityWork, primitiveWorkPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  ring_nf

end CurrentAFT.BinaryProfileKernel

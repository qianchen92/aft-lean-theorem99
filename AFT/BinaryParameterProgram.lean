import AFT.UnaryPolynomialCounters
import AFT.BinaryCounterDivision
import AFT.ParameterProgram
import AFT.ActualRootSamplerProgram

/-! Public parameter generation using explicit unary loop control and binary
long division. Trial-division candidates have polynomial numerical magnitude;
large Gaussian ticket integers never enter these unary counters. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram V7Calibration Polynomial
set_option backward.isDefEq.respectTransparency false

def securityCounter : ℕ → UnaryCounterResult
  | 0 => ⟨2,2⟩
  | 1 => ⟨2,3⟩
  | n+2 => ⟨n+2,3⟩

theorem securityCounter_value (n : ℕ) : (securityCounter n).count=max 2 n := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> simp [securityCounter]

theorem securityCounter_work (n : ℕ) : (securityCounter n).work≤3 := by
  cases n with
  | zero => decide
  | succ n => cases n <;> exact le_rfl

theorem lessCounter_decide (first second : ℕ) :
    (lessCounter first second).value=decide (first<second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [lessCounter_value,decide_eq_true_eq]

def binaryTrialDivisors (candidate : ℕ) : ℕ → ParameterProgram.CountedDecision
  | 0 => ⟨true,2⟩
  | length+1 =>
    let previous := binaryTrialDivisors candidate length
    let remainder := divideCounter candidate (length+2)
    ⟨previous.value && decide (remainder.remainder≠0),previous.work+remainder.work+5⟩

theorem binaryTrialDivisors_value (candidate length : ℕ) :
    (binaryTrialDivisors candidate length).value=(ParameterProgram.trialDivisors candidate length).value := by
  induction length with
  | zero => rfl
  | succ length ih =>
    simp only [binaryTrialDivisors,ParameterProgram.trialDivisors,ih,
      (divideCounter_value candidate (length+2) (by omega)).2]

theorem binaryTrialDivisors_work (candidate length : ℕ) :
    (binaryTrialDivisors candidate length).work≤2+length*(500*(candidate+length+4)^2+5) := by
  induction length with
  | zero => simp [binaryTrialDivisors]
  | succ length ih =>
    have hd := divideCounter_work candidate (length+2) (by omega)
    have hm : 500*(candidate+length+4)^2+5≤500*(candidate+(length+1)+4)^2+5 := by gcongr;omega
    have hi := ih.trans (Nat.add_le_add_left (Nat.mul_le_mul_left length hm) 2)
    have hd' : (divideCounter candidate (length+2)).work≤500*(candidate+(length+1)+4)^2 := by
      exact hd.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 2))
    simp only [binaryTrialDivisors]
    nlinarith

def binaryPrimeTest (candidate : ℕ) : ParameterProgram.CountedDecision :=
  let small := lessCounter candidate 2
  if small.value then ⟨false,small.work+2⟩ else
    let length := subtractCounter candidate 2
    let result := binaryTrialDivisors candidate length.count
    ⟨result.value,small.work+length.work+result.work+3⟩

theorem binaryPrimeTest_value (candidate : ℕ) :
    (binaryPrimeTest candidate).value=(ParameterProgram.primeTest candidate).value := by
  simp only [binaryPrimeTest,lessCounter_decide,decide_eq_true_eq,subtractCounter_value,
    binaryTrialDivisors_value,ParameterProgram.primeTest]
  split_ifs <;> rfl

def binaryPrimeWork (candidate : ℕ) : ℕ :=
  3*(candidate+2)+2+2*candidate+2+(2+candidate*(500*(candidate+candidate+4)^2+5))+3

theorem binaryPrimeTest_work (candidate : ℕ) : (binaryPrimeTest candidate).work≤binaryPrimeWork candidate := by
  have hs := lessCounter_work candidate 2
  have hd := subtractCounter_work_left candidate 2
  have ht := binaryTrialDivisors_work candidate (candidate-2)
  have ht' : (binaryTrialDivisors candidate (candidate-2)).work≤2+candidate*(500*(candidate+candidate+4)^2+5) := by
    apply ht.trans
    gcongr <;> omega
  simp only [binaryPrimeTest]
  split_ifs <;> simp only [subtractCounter_value]
  all_goals unfold binaryPrimeWork;omega

def binaryModulusTest (base candidate : ℕ) : ParameterProgram.CountedDecision :=
  let prime := binaryPrimeTest candidate
  let lower := lessCounter base candidate
  let upperBound := doubleCounter base
  let upper := lessCounter candidate upperBound.count.succ
  ⟨prime.value && lower.value && upper.value,prime.work+lower.work+upperBound.work+upper.work+4⟩

theorem binaryModulusTest_value (base candidate : ℕ) :
    (binaryModulusTest base candidate).value=(ParameterProgram.modulusTest base candidate).value := by
  simp only [binaryModulusTest,binaryPrimeTest_value,lessCounter_decide,doubleCounter_value,
    Nat.lt_succ_iff,ParameterProgram.modulusTest]

def binaryModulusTestWork (base candidate : ℕ) : ℕ :=
  binaryPrimeWork candidate+(3*(base+candidate)+2)+(3*base+1)+(3*(candidate+(2*base+1))+2)+4

theorem binaryModulusTest_work (base candidate : ℕ) :
    (binaryModulusTest base candidate).work≤binaryModulusTestWork base candidate := by
  have hp := binaryPrimeTest_work candidate
  have hl := lessCounter_work base candidate
  have hu := lessCounter_work candidate (2*base+1)
  simp only [binaryModulusTest,binaryModulusTestWork,doubleCounter_value,doubleCounter_work,Nat.succ_eq_add_one]
  omega

theorem binaryModulusTestWork_mono {base candidate larger : ℕ} (hc : candidate≤larger) :
    binaryModulusTestWork base candidate≤binaryModulusTestWork base larger := by
  unfold binaryModulusTestWork binaryPrimeWork
  gcongr

def binaryModulus (n : ℕ) : UnaryCounterResult :=
  let security := securityCounter n
  let base := powerCounter security.count 40
  let upper := doubleCounter base.count
  let result := ParameterProgram.boundedLeast (binaryModulusTest base.count) upper.count
  ⟨result.value,security.work+base.work+upper.work+result.work+4⟩

theorem binaryModulus_value (n : ℕ) : (binaryModulus n).count=Parameters.modulus n := by
  simp only [binaryModulus,securityCounter_value,powerCounter_value,doubleCounter_value]
  apply ParameterProgram.boundedLeast_exact
  · rw [binaryModulusTest_value]
    exact (ParameterProgram.modulusTest_value _ _).mpr (Parameters.modulus_spec n)
  · intro index hi
    rw [binaryModulusTest_value]
    apply Bool.eq_false_iff.mpr
    intro ht
    have hs := (ParameterProgram.modulusTest_value _ _).mp ht
    have hm : Parameters.modulus n ≤ index := by
      unfold Parameters.modulus
      exact Nat.find_min' _ hs
    omega
  · exact (Parameters.modulus_bounds n).2

def binaryModulusWork (n : ℕ) : ℕ :=
  3+powerCounterWork n 40+(3*n^40+1)+2*n^40*(binaryModulusTestWork (n^40) (2*n^40)+1)+4

theorem binaryModulus_work (n : ℕ) (hn : 2≤n) : (binaryModulus n).work≤binaryModulusWork n := by
  have hs : (securityCounter n).count=n := by rw [securityCounter_value,max_eq_right hn]
  have hw := securityCounter_work n
  have hp := powerCounter_work n 40
  have ht := ParameterProgram.boundedLeast_work_le (binaryModulusTest (n^40)) (2*n^40)
    (binaryModulusTestWork (n^40) (2*n^40)) (fun index hi =>
      (binaryModulusTest_work _ _).trans (binaryModulusTestWork_mono hi))
  simp only [binaryModulus,hs,powerCounter_value,doubleCounter_value,doubleCounter_work,binaryModulusWork]
  omega

end AFT.BinaryArithmetic

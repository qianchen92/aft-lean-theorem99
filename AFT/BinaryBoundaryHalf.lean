import AFT.BinaryLegCutoff
import AFT.BinaryCounterDivision
import AFT.BinarySignedAddition
import AFT.ActualSliceMeanProgram

/-! The true boundary half-width as signed binary digits, including every
integer parameter operation and the actual leg-cutoff search. -/
namespace AFT.BinaryArithmetic
open AFT.V7Calibration Polynomial

def boundarySecurityCounter : ℕ → UnaryCounterResult
  | 0 => ⟨2,2⟩
  | 1 => ⟨2,3⟩
  | n+2 => ⟨n+2,3⟩

theorem boundarySecurityCounter_value (n : ℕ) : (boundarySecurityCounter n).count=max 2 n := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> simp [boundarySecurityCounter]

theorem boundarySecurityCounter_work (n : ℕ) : (boundarySecurityCounter n).work ≤ 3 := by
  cases n with
  | zero => norm_num [boundarySecurityCounter]
  | succ n => cases n <;> norm_num [boundarySecurityCounter]

def binaryBoundaryHalf (constant n : ℕ) : SignedResult :=
  let security := boundarySecurityCounter n
  let safeSquare := multiplyCounter security.count security.count
  let margin := multiplyCounter 20 safeSquare.count
  let square := multiplyCounter n n
  let triple := multiplyCounter 3 square.count
  let root := differenceCounter triple.count 1
  let leg := binaryLegCutoff constant n
  let legRadius := differenceCounter leg.count 1
  let queue := differenceCounter square.count 1
  let first := addCounter root.count legRadius.count
  let radius := addCounter first.count queue.count
  let firstBits := canonicalCounter margin.count
  let secondBits := canonicalCounter radius.count
  let difference := signedAdd false true firstBits.digits secondBits.digits
  ⟨difference.negative,difference.digits,
    security.work+safeSquare.work+margin.work+square.work+triple.work+root.work+leg.work+
      legRadius.work+queue.work+first.work+radius.work+firstBits.work+secondBits.work+difference.work+14⟩

theorem binaryBoundaryHalf_value (constant n : ℕ) :
    signedValue (binaryBoundaryHalf constant n).negative (binaryBoundaryHalf constant n).digits=
      actualBoundaryHalfProgram constant n := by
  unfold binaryBoundaryHalf
  dsimp only
  rw [signedAdd_value]
  simp only [signedValue,canonicalCounter_value,boundarySecurityCounter_value,multiplyCounter_value,
    differenceCounter_value,addCounter_value,binaryLegCutoff_value,Bool.false_eq_true,↓reduceIte,
    actualBoundaryHalfProgram,actualSafeMarginProgram,pow_two]
  rfl

def boundaryCounterBound (constant n : ℕ) : ℕ := (constant+24)*(n+2)^2

theorem boundaryCounterBounds (constant n : ℕ) :
    n ≤ boundaryCounterBound constant n ∧
    max 2 n ≤ boundaryCounterBound constant n ∧
    max 2 n*max 2 n ≤ boundaryCounterBound constant n ∧
    20*(max 2 n*max 2 n) ≤ boundaryCounterBound constant n ∧
    n*n ≤ boundaryCounterBound constant n ∧
    3*(n*n) ≤ boundaryCounterBound constant n ∧
    actualLegCutoffProgram constant n ≤ boundaryCounterBound constant n ∧
    (3*(n*n)-1)+(actualLegCutoffProgram constant n-1)+(n*n-1) ≤ boundaryCounterBound constant n := by
  have hm : max 2 n ≤ n+2 := max_le (by omega) (by omega)
  have hsq := Nat.mul_le_mul hm hm
  have hl := actualLegCutoffProgram_le constant n
  unfold boundaryCounterBound
  simp only [pow_two] at hl ⊢
  constructor; nlinarith
  constructor; nlinarith
  constructor; nlinarith
  constructor; nlinarith
  constructor; nlinarith
  constructor; nlinarith
  constructor; nlinarith
  have h1 := Nat.sub_le (3*(n*n)) 1
  have h2 := Nat.sub_le (actualLegCutoffProgram constant n) 1
  have h3 := Nat.sub_le (n*n) 1
  nlinarith

theorem binaryBoundaryHalf_length (constant n : ℕ) :
    (binaryBoundaryHalf constant n).digits.length ≤ boundaryCounterBound constant n+1 := by
  have bounds := boundaryCounterBounds constant n
  have hsize (count : ℕ) : count.size ≤ count := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=count))
  have h := signedAdd_length false true
    (canonicalCounter (20*(max 2 n*max 2 n))).digits
    (canonicalCounter ((3*(n*n)-1)+(actualLegCutoffProgram constant n-1)+(n*n-1))).digits
  simp only [canonicalCounter_length] at h
  have ha := hsize (20*(max 2 n*max 2 n))
  have hb := hsize ((3*(n*n)-1)+(actualLegCutoffProgram constant n-1)+(n*n-1))
  have hs : max (20*(max 2 n*max 2 n)).size
      ((3*(n*n)-1)+(actualLegCutoffProgram constant n-1)+(n*n-1)).size ≤ boundaryCounterBound constant n := by omega
  have h' := h.trans (Nat.add_le_add_right hs 1)
  simpa only [binaryBoundaryHalf,boundarySecurityCounter_value,multiplyCounter_value,differenceCounter_value,
    addCounter_value,binaryLegCutoff_value] using h'

def binaryBoundaryHalfWork (constant n : ℕ) : ℕ :=
  binaryLegCutoffWork constant n+2000*(boundaryCounterBound constant n+1)^2+100

theorem binaryBoundaryHalf_work (constant n : ℕ) :
    (binaryBoundaryHalf constant n).work ≤ binaryBoundaryHalfWork constant n := by
  rcases boundaryCounterBounds constant n with ⟨hn,hs,hss,hm,hnn,ht,hl,hr⟩
  let bound := boundaryCounterBound constant n
  have hsec := boundarySecurityCounter_work n
  have hleg := binaryLegCutoff_work constant n
  have hroot := differenceCounter_work (3*(n*n)) 1
  have hrl := differenceCounter_work (actualLegCutoffProgram constant n) 1
  have hqueue := differenceCounter_work (n*n) 1
  have hrootcount := Nat.sub_le (3*(n*n)) 1
  have hrcount := Nat.sub_le (actualLegCutoffProgram constant n) 1
  have hqcount := Nat.sub_le (n*n) 1
  have ha := canonicalCounter_work (20*(max 2 n*max 2 n))
  have hb := canonicalCounter_work ((3*(n*n)-1)+(actualLegCutoffProgram constant n-1)+(n*n-1))
  have ha' : (canonicalCounter (20*(max 2 n*max 2 n))).work ≤ 50*(bound+1)^2 := ha.trans (by gcongr)
  have hb' : (canonicalCounter ((3*(n*n)-1)+(actualLegCutoffProgram constant n-1)+(n*n-1))).work ≤ 50*(bound+1)^2 := hb.trans (by gcongr)
  have hsize (count : ℕ) : count.size ≤ count := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=count))
  have hlen : max (canonicalCounter (20*(max 2 n*max 2 n))).digits.length
      (canonicalCounter ((3*(n*n)-1)+(actualLegCutoffProgram constant n-1)+(n*n-1))).digits.length ≤ bound := by
    simp only [canonicalCounter_length]
    exact max_le ((hsize _).trans hm) ((hsize _).trans hr)
  have hd := (signedAdd_work false true
    (canonicalCounter (20*(max 2 n*max 2 n))).digits
    (canonicalCounter ((3*(n*n)-1)+(actualLegCutoffProgram constant n-1)+(n*n-1))).digits).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 20 hlen) 8)
  have hmult : max 2 n*(2*max 2 n+3) ≤ bound*(2*bound+3) := by gcongr
  have hmult' : n*(2*n+3) ≤ bound*(2*bound+3) := by gcongr
  unfold binaryBoundaryHalf binaryBoundaryHalfWork
  simp only [boundarySecurityCounter_value,multiplyCounter_work,multiplyCounter_value,differenceCounter_value,
    binaryLegCutoff_value,addCounter_work,addCounter_value]
  change _ ≤ binaryLegCutoffWork constant n+2000*(bound+1)^2+100
  nlinarith

noncomputable def boundaryCounterPolynomial (constant : ℕ) : Polynomial ℕ :=
  C (constant+24)*(X+2)^2
noncomputable def binaryBoundaryHalfPolynomial (constant : ℕ) : Polynomial ℕ :=
  binaryLegCutoffPolynomial constant+2000*(boundaryCounterPolynomial constant+1)^2+100

@[simp] theorem boundaryCounterPolynomial_eval (constant n : ℕ) :
    (boundaryCounterPolynomial constant).eval n=boundaryCounterBound constant n := by
  simp [boundaryCounterPolynomial,boundaryCounterBound]
@[simp] theorem binaryBoundaryHalfPolynomial_eval (constant n : ℕ) :
    (binaryBoundaryHalfPolynomial constant).eval n=binaryBoundaryHalfWork constant n := by
  simp [binaryBoundaryHalfPolynomial,binaryBoundaryHalfWork]

end AFT.BinaryArithmetic

import AFT.BinaryGaussianPolynomials
import AFT.BinaryGaussianInputs
import AFT.BinaryWindowControl
import AFT.BinarySamplingPolynomials
import AFT.GaussianWindowHeight
import AFT.RationalWindowTickets

/-! # Binary Gaussian evaluation on arbitrary bounded windows

The width is stored binary input. Coordinates, precision counters, every
Gaussian evaluation, and array normalization are executed explicitly.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics GaussianSource FiniteConvolutionProgram Polynomial
open scoped BigOperators

theorem gaussianExpScale_le_budget (width : ℚ) (point : ℤ) (bits budget : ℕ) (hb : 1≤ budget)
    (h0 : 0≤ gaussianRatio width point) (hr : gaussianRatio width point≤ budget) :
    gaussianExpScale width point bits≤ 11*budget := by
  have hp := mul_le_mul_of_nonneg_right (piApprox_le_five (gaussianPiPrecision width point bits)) h0
  have hmax : max (piApprox (gaussianPiPrecision width point bits)*gaussianRatio width point) 0≤
      ((5*budget : ℕ) : ℚ) := by
    apply max_le
    · push_cast
      nlinarith
    · positivity
  have hc : ⌈max (piApprox (gaussianPiPrecision width point bits)*gaussianRatio width point) 0⌉₊≤5*budget :=
    Nat.ceil_le.mpr hmax
  unfold gaussianExpScale expScale
  omega

def binaryWindowPoint (width : RationalBits) (cutoff precision index : ℕ) : RationalResult :=
  let point := integerDifference index cutoff
  let encoded := ofUnaryInteger point.value
  let result := gaussian width encoded.data precision
  ⟨result.data,point.work+encoded.work+result.work+3⟩

theorem binaryWindowPoint_value (width : RationalBits) (cutoff precision index : ℕ) :
    (binaryWindowPoint width cutoff precision index).data.decode=
      gaussianApprox width.decode ((index : ℤ)-(cutoff : ℤ)) precision := by
  simp only [binaryWindowPoint,gaussian_value _ _ _ _ (ofUnaryInteger_value _),integerDifference_value]

def binaryWindowPointWork (budget : ℕ) : ℕ :=
  60*(budget+1)^2+gaussianWork budget budget budget (11*budget) (4*budget)+10*budget+12

theorem binaryWindowPoint_work (width : RationalBits) (cutoff precision budget : ℕ)
    (hb : 2≤ budget) (hc : cutoff≤ budget) (hp : precision≤4*budget)
    (hw : HeightBound width.decode budget)
    (hr : ∀ point : Window cutoff,0≤ gaussianRatio width.decode point ∧ gaussianRatio width.decode point≤ budget)
    (index : Fin (2*cutoff+1)) :
    (binaryWindowPoint width cutoff precision index).work≤ binaryWindowPointWork budget := by
  let point := windowIndexEquiv cutoff index
  have he : (integerDifference index.val cutoff).value=point.val := by rw [integerDifference_value];rfl
  have hi := index.isLt
  have habs : point.val.natAbs≤ cutoff := by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    rw [← Nat.cast_le (α := ℤ),Int.natCast_natAbs]
    exact abs_le.mpr ⟨hl,hu⟩
  have hh : HeightBound (ofUnaryInteger point.val).data.decode budget := by
    rw [ofUnaryInteger_value]
    exact HeightBound.of_int ((habs.trans hc).trans (Nat.lt_two_pow_self (n:=budget)).le)
  have wg := gaussian_work width (ofUnaryInteger point.val).data point.val budget budget precision
    hw hh (ofUnaryInteger_value _)
  have hg : gaussianGuard width.decode point≤ budget := Nat.ceil_le.mpr (hr point).2
  have hs := gaussianExpScale_le_budget width.decode point precision budget (by omega) (hr point).1 (hr point).2
  have wg' := wg.trans (gaussianWork_mono le_rfl le_rfl hg hs hp)
  have we := ofUnaryInteger_work point.val
  have wc := integerDifference_work index.val cutoff
  have wb := Nat.pow_le_pow_left (show point.val.natAbs+1≤budget+1 by omega) 2
  simp only [binaryWindowPoint,he,binaryWindowPointWork]
  nlinarith

def binaryWindowRaw (width : RationalBits) (cutoff bits : ℕ) : ArrayResult (2*cutoff+1) :=
  let doubled := doubleCounter cutoff
  let count := doubled.count.succ
  let precision := addCounter bits count
  let raw := buildArray count (fun index => binaryWindowPoint width cutoff precision.count.succ index.val)
  ⟨Vector.cast (by dsimp only [count,doubled];rw [doubleCounter_value]) raw.data,doubled.work+precision.work+raw.work+4⟩

theorem binaryWindowRaw_value (width : RationalBits) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    ((binaryWindowRaw width cutoff bits).data.get index).decode=
      windowApproxRaw width.decode cutoff bits (windowIndexEquiv cutoff index) := by
  simp only [binaryWindowRaw,Vector.get_cast,buildArray_get,binaryWindowPoint_value,Fin.val_cast,
    addCounter_value,doubleCounter_value]
  rfl

def binaryWindowRawWork (budget : ℕ) : ℕ :=
  (2*budget+1)*(binaryWindowPointWork budget+2)+5*budget+10

theorem binaryWindowRaw_work (width : RationalBits) (cutoff bits budget : ℕ)
    (hb : 2≤ budget) (hc : cutoff≤ budget) (hp : bits≤budget)
    (hw : HeightBound width.decode budget)
    (hr : ∀ point : Window cutoff,0≤ gaussianRatio width.decode point ∧ gaussianRatio width.decode point≤ budget) :
    (binaryWindowRaw width cutoff bits).work≤ binaryWindowRawWork budget := by
  have hcount : (doubleCounter cutoff).count.succ=2*cutoff+1 := by rw [doubleCounter_value]
  have hprec : (addCounter bits (doubleCounter cutoff).count.succ).count.succ≤4*budget := by
    rw [addCounter_value,hcount];omega
  have hentry (index : Fin (doubleCounter cutoff).count.succ) :
      (binaryWindowPoint width cutoff (addCounter bits (doubleCounter cutoff).count.succ).count.succ index).work≤
        binaryWindowPointWork budget :=
    binaryWindowPoint_work width cutoff _ budget hb hc hprec hw hr (Fin.cast hcount index)
  have wr := buildArray_work (doubleCounter cutoff).count.succ (binaryWindowPointWork budget)
    (fun index => binaryWindowPoint width cutoff (addCounter bits (doubleCounter cutoff).count.succ).count.succ index.val) hentry
  simp only [binaryWindowRaw,doubleCounter_work,addCounter_work,binaryWindowRawWork]
  have hcount' : (doubleCounter cutoff).count.succ≤ 2*budget+1 := by omega
  nlinarith

theorem binaryWindowRaw_height (width : RationalBits) (cutoff bits budget : ℕ)
    (hb : 2≤ budget) (hc : cutoff≤ budget) (hp : bits≤budget)
    (hr : ∀ point : Window cutoff,0≤ gaussianRatio width.decode point ∧ gaussianRatio width.decode point≤ budget)
    (hh : ∀ point : Window cutoff,HeightBound (gaussianRatio width.decode point) (3*budget))
    (index : Fin (2*cutoff+1)) :
    HeightBound ((binaryWindowRaw width cutoff bits).data.get index).decode (100000000*budget^5) := by
  rw [binaryWindowRaw_value]
  exact gaussianApprox_height_of_budget width.decode _ _ budget hb
    (by unfold windowApproxPrecision;omega) (hr _).1 (hr _).2 (hh _)

def binaryWindowWeights (width : RationalBits) (cutoff bits : ℕ) : ArrayResult (2*cutoff+1) :=
  let raw := binaryWindowRaw width cutoff bits
  let normalized := normalizeArray raw.data
  ⟨normalized.data,raw.work+normalized.work+2⟩

theorem binaryWindowWeights_value (width : RationalBits) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    ((binaryWindowWeights width cutoff bits).data.get index).decode=windowGaussianWeights width.decode cutoff bits index := by
  simp only [binaryWindowWeights,normalizeArray_value,binaryWindowRaw_value,windowGaussianWeights,windowApproxWeight]
  congr 1
  exact (windowIndexEquiv cutoff).sum_comp _

def binaryWindowWork (budget : ℕ) : ℕ :=
  binaryWindowRawWork budget+normalizeArrayWork (2*budget+1) (100000000*budget^5)+2

theorem binaryWindowWeights_work (width : RationalBits) (cutoff bits budget : ℕ)
    (hb : 2≤ budget) (hc : cutoff≤ budget) (hp : bits≤budget)
    (hw : HeightBound width.decode budget)
    (hr : ∀ point : Window cutoff,0≤ gaussianRatio width.decode point ∧ gaussianRatio width.decode point≤ budget)
    (hh : ∀ point : Window cutoff,HeightBound (gaussianRatio width.decode point) (3*budget)) :
    (binaryWindowWeights width cutoff bits).work≤ binaryWindowWork budget := by
  have wr := binaryWindowRaw_work width cutoff bits budget hb hc hp hw hr
  have wn := normalizeArray_work (binaryWindowRaw width cutoff bits).data (100000000*budget^5)
    (binaryWindowRaw_height width cutoff bits budget hb hc hp hr hh)
  have wm := wn.trans (normalizeArrayWork_mono (show 2*cutoff+1≤2*budget+1 by omega) (le_refl (100000000*budget^5)))
  simp only [binaryWindowWeights,binaryWindowWork]
  omega

theorem binaryWindowWeights_height (width : RationalBits) (cutoff bits budget : ℕ)
    (hb : 2≤ budget) (hc : cutoff≤ budget) (hp : bits≤budget)
    (hr : ∀ point : Window cutoff,0≤ gaussianRatio width.decode point ∧ gaussianRatio width.decode point≤ budget)
    (hh : ∀ point : Window cutoff,HeightBound (gaussianRatio width.decode point) (3*budget))
    (index : Fin (2*cutoff+1)) :
    HeightBound ((binaryWindowWeights width cutoff bits).data.get index).decode (500000000*budget^6) := by
  rw [binaryWindowWeights_value]
  exact windowApproxWeight_height_of_budget width.decode cutoff bits budget hb hc hp
    (fun point => (hr point).1) (fun point => (hr point).2) hh _

noncomputable def binaryWindowPointPolynomial (budget : Polynomial ℕ) : Polynomial ℕ :=
  60*(budget+1)^2+gaussianWorkPolynomial budget budget budget (11*budget) (4*budget)+10*budget+12
noncomputable def binaryWindowRawPolynomial (budget : Polynomial ℕ) : Polynomial ℕ :=
  (2*budget+1)*(binaryWindowPointPolynomial budget+2)+5*budget+10
noncomputable def binaryWindowPolynomial (budget : Polynomial ℕ) : Polynomial ℕ :=
  binaryWindowRawPolynomial budget+normalizeArrayWorkPolynomial (2*budget+1) (100000000*budget^5)+2

@[simp] theorem binaryWindowPointPolynomial_eval (budget : Polynomial ℕ) (n : ℕ) :
    (binaryWindowPointPolynomial budget).eval n=binaryWindowPointWork (budget.eval n) := by
  simp only [binaryWindowPointPolynomial,binaryWindowPointWork,eval_add,eval_mul,eval_pow,eval_one,eval_ofNat,
    gaussianWorkPolynomial_eval]
@[simp] theorem binaryWindowRawPolynomial_eval (budget : Polynomial ℕ) (n : ℕ) :
    (binaryWindowRawPolynomial budget).eval n=binaryWindowRawWork (budget.eval n) := by
  simp only [binaryWindowRawPolynomial,binaryWindowRawWork,eval_add,eval_mul,eval_one,eval_ofNat,
    binaryWindowPointPolynomial_eval]
@[simp] theorem binaryWindowPolynomial_eval (budget : Polynomial ℕ) (n : ℕ) :
    (binaryWindowPolynomial budget).eval n=binaryWindowWork (budget.eval n) := by
  simp only [binaryWindowPolynomial,binaryWindowWork,eval_add,eval_mul,eval_pow,eval_one,eval_ofNat,
    binaryWindowRawPolynomial_eval,normalizeArrayWorkPolynomial_eval]

end AFT.BinaryArithmetic.RationalBits

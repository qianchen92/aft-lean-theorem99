import CurrentAFT.BinaryGaussianAverage

/-! # One-dimensional Gaussian averages with charged binary lookup and sums -/
namespace CurrentAFT.BinaryWindowAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def term {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult)
    (index : Fin count) : RationalResult :=
  let weight := readVector zero weights index
  let value := kernel index
  let result := RationalBits.multiply weight.value value.data
  ⟨result.data, weight.work + value.work + result.work + 3⟩

theorem term_value {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult) (index : Fin count) :
    (term weights kernel index).data.decode = (weights.get index).decode*(kernel index).data.decode := by
  simp only [term, RationalBits.multiply_value, readVector_value]

def termWork (count gh kh kw : ℕ) : ℕ := 3*count+3+kw+primitiveWorkBound (gh+kh)+3

theorem term_bounds {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult)
    (index : Fin count) (gh kh kw : ℕ) (hw : HeightBound (weights.get index).decode gh)
    (hh : HeightBound (kernel index).data.decode kh) (hk : (kernel index).work ≤ kw) :
    HeightBound (term weights kernel index).data.decode (gh+kh) ∧
      (term weights kernel index).work ≤ termWork count gh kh kw := by
  let weight := readVector zero weights index
  let value := kernel index
  have hweight : HeightBound weight.value.decode gh := by rw [readVector_value]; exact hw
  have wweight : weight.work ≤ 3*count+3 := readVector_work zero weights index
  have wvalue : value.work ≤ kw := hk
  have wresult := RationalBits.multiply_work weight.value value.data (gh+kh)
    (hweight.mono (by omega)) (hh.mono (by omega))
  constructor
  · rw [term_value]; exact hw.mul hh
  · change weight.work + value.work + (RationalBits.multiply weight.value value.data).work + 3 ≤ _
    unfold termWork
    omega

def sum {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult) : RationalResult :=
  sumFin count (term weights kernel)

theorem sum_value {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult) :
    (sum weights kernel).data.decode = ∑ index, (weights.get index).decode*(kernel index).data.decode := by
  simp only [sum, sumFin_value, term_value]

def sumHeight (count gh kh : ℕ) : ℕ := count*(gh+kh+1)
def sumWork (count gh kh kw : ℕ) : ℕ :=
  count*(termWork count gh kh kw+primitiveWorkBound ((count+1)*(gh+kh+1))+2)+2

theorem sum_bounds {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → RationalResult)
    (gh kh kw : ℕ) (hw : ∀ index, HeightBound (weights.get index).decode gh)
    (hh : ∀ index, HeightBound (kernel index).data.decode kh) (hk : ∀ index, (kernel index).work ≤ kw) :
    HeightBound (sum weights kernel).data.decode (sumHeight count gh kh) ∧
      (sum weights kernel).work ≤ sumWork count gh kh kw := by
  have ht (index : Fin count) := term_bounds weights kernel index gh kh kw (hw index) (hh index) (hk index)
  exact ⟨sumFin_height _ _ _ (fun index => (ht index).1), sumFin_work _ _ _ _
    (fun index => (ht index).1) (fun index => (ht index).2)⟩

def evaluate (security cutoff bits : ℕ) (kernel : Fin (2*cutoff+1) → RationalResult) : RationalResult :=
  let weights := CurrentGaussianBits.table security cutoff bits
  let result := sum weights.data kernel
  ⟨result.data, weights.work + result.work + 2⟩

theorem evaluate_value (security cutoff bits : ℕ) (kernel : Fin (2*cutoff+1) → RationalResult) :
    (evaluate security cutoff bits kernel).data.decode =
      ∑ index, windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits index*(kernel index).data.decode := by
  simp only [evaluate, sum_value, CurrentGaussianBits.table_value]

def evaluateWork (security cutoff bits kh kw : ℕ) : ℕ :=
  CurrentGaussianBits.tableWork security bits +
    sumWork (2*cutoff+1) (BinaryGaussianAverage.gaussianHeight security bits) kh kw + 2

theorem evaluate_bounds (security cutoff bits : ℕ) (kernel : Fin (2*cutoff+1) → RationalResult) (kh kw : ℕ)
    (hcutoff : cutoff ≤ (security+2)^2) (hh : ∀ index, HeightBound (kernel index).data.decode kh)
    (hk : ∀ index, (kernel index).work ≤ kw) :
    HeightBound (evaluate security cutoff bits kernel).data.decode
      (sumHeight (2*cutoff+1) (BinaryGaussianAverage.gaussianHeight security bits) kh) ∧
      (evaluate security cutoff bits kernel).work ≤ evaluateWork security cutoff bits kh kw := by
  have hs := sum_bounds (CurrentGaussianBits.table security cutoff bits).data kernel
    (BinaryGaussianAverage.gaussianHeight security bits) kh kw
    (CurrentGaussianBits.table_height security cutoff bits hcutoff) hh hk
  exact ⟨hs.1, Nat.add_le_add_right (Nat.add_le_add (CurrentGaussianBits.table_work security cutoff bits hcutoff) hs.2) 2⟩

theorem sumWork_mono {count count' gh gh' kh kh' kw kw' : ℕ}
    (hc : count ≤ count') (hg : gh ≤ gh') (hh : kh ≤ kh') (hw : kw ≤ kw') :
    sumWork count gh kh kw ≤ sumWork count' gh' kh' kw' := by
  unfold sumWork termWork primitiveWorkBound
  gcongr

noncomputable def termWorkPolynomial (count gh kh kw : Polynomial ℕ) : Polynomial ℕ :=
  3*count+3+kw+primitiveWorkPolynomial (gh+kh)+3
noncomputable def sumWorkPolynomial (count gh kh kw : Polynomial ℕ) : Polynomial ℕ :=
  count*(termWorkPolynomial count gh kh kw+primitiveWorkPolynomial ((count+1)*(gh+kh+1))+2)+2
noncomputable def evaluateWorkPolynomial (cutoff precision kh kw : Polynomial ℕ) : Polynomial ℕ :=
  CurrentGaussianBits.workPolynomial precision +
    sumWorkPolynomial (2*cutoff+1) (500000000*((Polynomial.X+2)^2+precision+2)^6) kh kw + 2

theorem evaluateWorkPolynomial_eval (cutoff precision kh kw : Polynomial ℕ) (security : ℕ) :
    (evaluateWorkPolynomial cutoff precision kh kw).eval security =
      evaluateWork security (cutoff.eval security) (precision.eval security) (kh.eval security) (kw.eval security) := by
  simp only [evaluateWorkPolynomial, sumWorkPolynomial, termWorkPolynomial, evaluateWork, sumWork, termWork,
    BinaryGaussianAverage.gaussianHeight, CurrentGaussianBits.budget, CurrentGaussianBits.workPolynomial_eval,
    primitiveWorkPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]

end CurrentAFT.BinaryWindowAverage

import CurrentAFT.CurrentGaussianBits

/-! # Materialized binary averaging against two current Gaussian edges -/
namespace CurrentAFT.BinaryGaussianAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def term {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → Fin count → RationalResult)
    (left right : Fin count) : RationalResult :=
  let first := readVector zero weights left
  let second := readVector zero weights right
  let response := kernel left right
  let probability := RationalBits.multiply first.value second.value
  let result := RationalBits.multiply probability.data response.data
  ⟨result.data, first.work + second.work + response.work + probability.work + result.work + 5⟩

theorem term_value {count : ℕ} (weights : Vector RationalBits count)
    (kernel : Fin count → Fin count → RationalResult) (left right : Fin count) :
    (term weights kernel left right).data.decode =
      (weights.get left).decode*(weights.get right).decode*(kernel left right).data.decode := by
  simp only [term, RationalBits.multiply_value, readVector_value]

def termHeight (gaussianHeight kernelHeight : ℕ) : ℕ := 2*gaussianHeight+kernelHeight
def termWork (count gaussianHeight kernelHeight kernelWork : ℕ) : ℕ :=
  2*(3*count+3) + kernelWork + 2*primitiveWorkBound (termHeight gaussianHeight kernelHeight)+5

theorem term_bounds {count : ℕ} (weights : Vector RationalBits count)
    (kernel : Fin count → Fin count → RationalResult) (left right : Fin count)
    (gaussianHeight kernelHeight kernelWork : ℕ)
    (hw : ∀ index, HeightBound (weights.get index).decode gaussianHeight)
    (hh : HeightBound (kernel left right).data.decode kernelHeight) (hk : (kernel left right).work ≤ kernelWork) :
    HeightBound (term weights kernel left right).data.decode (termHeight gaussianHeight kernelHeight) ∧
      (term weights kernel left right).work ≤ termWork count gaussianHeight kernelHeight kernelWork := by
  let first := readVector zero weights left
  let second := readVector zero weights right
  let response := kernel left right
  let probability := RationalBits.multiply first.value second.value
  have hf : HeightBound first.value.decode gaussianHeight := by rw [readVector_value]; exact hw left
  have hs : HeightBound second.value.decode gaussianHeight := by rw [readVector_value]; exact hw right
  have hp : HeightBound probability.data.decode (2*gaussianHeight) := by
    rw [RationalBits.multiply_value]
    exact (hf.mul hs).mono (by omega)
  have wf : first.work ≤ 3*count+3 := readVector_work zero weights left
  have ws : second.work ≤ 3*count+3 := readVector_work zero weights right
  have wr : response.work ≤ kernelWork := hk
  have wp : probability.work ≤ primitiveWorkBound (termHeight gaussianHeight kernelHeight) :=
    RationalBits.multiply_work first.value second.value _
      (hf.mono (by unfold termHeight; omega)) (hs.mono (by unfold termHeight; omega))
  have wresult := RationalBits.multiply_work probability.data response.data (termHeight gaussianHeight kernelHeight)
    (hp.mono (by unfold termHeight; omega)) (hh.mono (by unfold termHeight; omega))
  constructor
  · change HeightBound (RationalBits.multiply probability.data response.data).data.decode _
    rw [RationalBits.multiply_value]
    exact hp.mul hh
  · change first.work + second.work + response.work + probability.work +
      (RationalBits.multiply probability.data response.data).work + 5 ≤ _
    unfold termWork
    omega

def sum {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → Fin count → RationalResult) : RationalResult :=
  sumFin count (fun left => sumFin count (fun right => term weights kernel left right))

theorem sum_value {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → Fin count → RationalResult) :
    (sum weights kernel).data.decode =
      ∑ left, ∑ right, (weights.get left).decode*(weights.get right).decode*(kernel left right).data.decode := by
  simp only [sum, sumFin_value, term_value]

def sumHeight (count gaussianHeight kernelHeight : ℕ) : ℕ := count*(count*(termHeight gaussianHeight kernelHeight+1)+1)
def sumWork (count gaussianHeight kernelHeight kernelWork : ℕ) : ℕ :=
  count*(count*(termWork count gaussianHeight kernelHeight kernelWork +
    primitiveWorkBound ((count+1)*(termHeight gaussianHeight kernelHeight+1))+2)+2 +
    primitiveWorkBound ((count+1)*(count*(termHeight gaussianHeight kernelHeight+1)+1))+2)+2

theorem sum_bounds {count : ℕ} (weights : Vector RationalBits count) (kernel : Fin count → Fin count → RationalResult)
    (gaussianHeight kernelHeight kernelWork : ℕ)
    (hw : ∀ index, HeightBound (weights.get index).decode gaussianHeight)
    (hh : ∀ left right, HeightBound (kernel left right).data.decode kernelHeight)
    (hk : ∀ left right, (kernel left right).work ≤ kernelWork) :
    HeightBound (sum weights kernel).data.decode (sumHeight count gaussianHeight kernelHeight) ∧
      (sum weights kernel).work ≤ sumWork count gaussianHeight kernelHeight kernelWork := by
  have ht (left right : Fin count) := term_bounds weights kernel left right gaussianHeight kernelHeight kernelWork
    hw (hh left right) (hk left right)
  have hi (left : Fin count) := sumFin_height count (termHeight gaussianHeight kernelHeight)
    (fun right => term weights kernel left right) (fun right => (ht left right).1)
  have wi (left : Fin count) := sumFin_work count (termHeight gaussianHeight kernelHeight)
    (termWork count gaussianHeight kernelHeight kernelWork)
    (fun right => term weights kernel left right) (fun right => (ht left right).1) (fun right => (ht left right).2)
  exact ⟨sumFin_height _ _ _ hi, sumFin_work _ _ _ _ hi wi⟩

def evaluate (security cutoff bits : ℕ) (kernel : Fin (2*cutoff+1) → Fin (2*cutoff+1) → RationalResult) : RationalResult :=
  let weights := CurrentGaussianBits.table security cutoff bits
  let result := sum weights.data kernel
  ⟨result.data, weights.work + result.work + 2⟩

theorem evaluate_value (security cutoff bits : ℕ) (kernel : Fin (2*cutoff+1) → Fin (2*cutoff+1) → RationalResult) :
    (evaluate security cutoff bits kernel).data.decode =
      ∑ left, ∑ right, windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits left *
        windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits right *
        (kernel left right).data.decode := by
  simp only [evaluate, sum_value, CurrentGaussianBits.table_value]

def gaussianHeight (security bits : ℕ) : ℕ := 500000000*(CurrentGaussianBits.budget security bits)^6
def evaluateWork (security cutoff bits kernelHeight kernelWork : ℕ) : ℕ :=
  CurrentGaussianBits.tableWork security bits + sumWork (2*cutoff+1) (gaussianHeight security bits) kernelHeight kernelWork + 2

theorem evaluate_bounds (security cutoff bits : ℕ)
    (kernel : Fin (2*cutoff+1) → Fin (2*cutoff+1) → RationalResult) (kernelHeight kernelWork : ℕ)
    (hcutoff : cutoff ≤ (security+2)^2)
    (hh : ∀ left right, HeightBound (kernel left right).data.decode kernelHeight)
    (hk : ∀ left right, (kernel left right).work ≤ kernelWork) :
    HeightBound (evaluate security cutoff bits kernel).data.decode
      (sumHeight (2*cutoff+1) (gaussianHeight security bits) kernelHeight) ∧
      (evaluate security cutoff bits kernel).work ≤ evaluateWork security cutoff bits kernelHeight kernelWork := by
  have hs := sum_bounds (CurrentGaussianBits.table security cutoff bits).data kernel (gaussianHeight security bits)
    kernelHeight kernelWork (CurrentGaussianBits.table_height security cutoff bits hcutoff) hh hk
  constructor
  · exact hs.1
  · exact Nat.add_le_add_right (Nat.add_le_add (CurrentGaussianBits.table_work security cutoff bits hcutoff) hs.2) 2

theorem sumWork_mono {count count' gh gh' kh kh' kw kw' : ℕ}
    (hc : count ≤ count') (hg : gh ≤ gh') (hh : kh ≤ kh') (hw : kw ≤ kw') :
    sumWork count gh kh kw ≤ sumWork count' gh' kh' kw' := by
  unfold sumWork termWork termHeight primitiveWorkBound
  gcongr

noncomputable def termHeightPolynomial (gh kh : Polynomial ℕ) : Polynomial ℕ := 2*gh+kh
noncomputable def termWorkPolynomial (count gh kh kw : Polynomial ℕ) : Polynomial ℕ :=
  2*(3*count+3)+kw+2*primitiveWorkPolynomial (termHeightPolynomial gh kh)+5
noncomputable def sumWorkPolynomial (count gh kh kw : Polynomial ℕ) : Polynomial ℕ :=
  count*(count*(termWorkPolynomial count gh kh kw +
    primitiveWorkPolynomial ((count+1)*(termHeightPolynomial gh kh+1))+2)+2 +
    primitiveWorkPolynomial ((count+1)*(count*(termHeightPolynomial gh kh+1)+1))+2)+2
noncomputable def evaluateWorkPolynomial (cutoff precision kh kw : Polynomial ℕ) : Polynomial ℕ :=
  CurrentGaussianBits.workPolynomial precision +
    sumWorkPolynomial (2*cutoff+1) (500000000*((Polynomial.X+2)^2+precision+2)^6) kh kw + 2

theorem evaluateWorkPolynomial_eval (cutoff precision kh kw : Polynomial ℕ) (security : ℕ) :
    (evaluateWorkPolynomial cutoff precision kh kw).eval security =
      evaluateWork security (cutoff.eval security) (precision.eval security) (kh.eval security) (kw.eval security) := by
  simp only [evaluateWorkPolynomial, sumWorkPolynomial, termWorkPolynomial, termHeightPolynomial,
    evaluateWork, sumWork, termWork, termHeight, gaussianHeight, CurrentGaussianBits.budget,
    CurrentGaussianBits.workPolynomial_eval, primitiveWorkPolynomial_eval, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]

end CurrentAFT.BinaryGaussianAverage

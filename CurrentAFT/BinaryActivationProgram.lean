import CurrentAFT.CurrentGaussianBits
import CurrentAFT.LocalPairProgram

/-! # The actual activation computed from a stored scalar Gaussian table -/
namespace CurrentAFT.BinaryActivationProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter powerCounter differenceCounter
  Parameters.base Parameters.sourceCutoff

def cutoff (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let last := differenceCounter square.count 1
  ⟨last.count, base.work + square.work + last.work + 3⟩

theorem cutoff_value (security : ℕ) : (cutoff security).count = (security+2)^2-1 := by
  simp only [cutoff, differenceCounter_value, powerCounter_value, addCounter_value]

def cutoffWork (security : ℕ) : ℕ := 2*security+1 + powerCounterWork (security+2) 2 + (2*(security+2)^2+1) + 3

theorem cutoff_work (security : ℕ) : (cutoff security).work ≤ cutoffWork security := by
  have hp := powerCounter_work (security+2) 2
  have hd := differenceCounter_work ((security+2)^2) 1
  simp only [cutoff, addCounter_value, powerCounter_value, addCounter_work, cutoffWork]
  omega

def current (security bits : ℕ) : RationalResult :=
  let window := cutoff security
  let table := CurrentGaussianBits.table security window.count bits
  let zeroAtom := readVector zero table.data ⟨window.count, by omega⟩
  let result := RationalBits.multiply half zeroAtom.value
  ⟨result.data, window.work + table.work + zeroAtom.work + result.work + 4⟩

theorem zero_index (window : ℕ) : windowIndexEquiv window ⟨window, by omega⟩ = windowZero window := by
  apply Subtype.ext
  simp only [windowIndexEquiv, Equiv.coe_fn_mk, windowZero]
  omega

theorem current_value (security bits : ℕ) :
    (current security bits).data.decode = LocalPairProgram.activationApprox security bits := by
  simp only [current, RationalBits.multiply_value, half_value, readVector_value,
    CurrentGaussianBits.table_value, windowGaussianWeights, zero_index]
  have hc : (cutoff security).count = Parameters.sourceCutoff security-1 := by
    simp only [cutoff_value, Parameters.sourceCutoff, Parameters.base]
  rw [hc]
  rfl

def currentHeight (security bits : ℕ) : ℕ := 500000000*(CurrentGaussianBits.budget security bits)^6+2
def currentWork (security bits : ℕ) : ℕ := cutoffWork security + CurrentGaussianBits.tableWork security bits +
  (3*(2*(security+2)^2+1)+3) + primitiveWorkBound (currentHeight security bits) + 4

theorem current_bounds (security bits : ℕ) :
    HeightBound (current security bits).data.decode (currentHeight security bits) ∧
      (current security bits).work ≤ currentWork security bits := by
  let window := cutoff security
  let table := CurrentGaussianBits.table security window.count bits
  let zeroAtom := readVector zero table.data ⟨window.count, by omega⟩
  have hc : window.count ≤ (security+2)^2 := by rw [cutoff_value]; omega
  have ht : HeightBound zeroAtom.value.decode (500000000*(CurrentGaussianBits.budget security bits)^6) := by
    rw [readVector_value]
    exact CurrentGaussianBits.table_height security window.count bits hc _
  have hh : HeightBound half.decode 2 := by rw [half_value]; norm_num [HeightBound]
  have ww : window.work ≤ cutoffWork security := cutoff_work security
  have wt : table.work ≤ CurrentGaussianBits.tableWork security bits := CurrentGaussianBits.table_work security _ bits hc
  have wr : zeroAtom.work ≤ 3*(2*(security+2)^2+1)+3 :=
    (readVector_work zero table.data _).trans (by omega)
  have wp := RationalBits.multiply_work half zeroAtom.value (currentHeight security bits)
    (hh.mono (by unfold currentHeight; omega)) (ht.mono (by unfold currentHeight; omega))
  constructor
  · change HeightBound (RationalBits.multiply half zeroAtom.value).data.decode _
    rw [RationalBits.multiply_value]
    exact (hh.mul ht).mono (by unfold currentHeight; omega)
  · change window.work + table.work + zeroAtom.work + (RationalBits.multiply half zeroAtom.value).work + 4 ≤ _
    unfold currentWork
    omega

noncomputable def currentHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  500000000*((Polynomial.X+2)^2+precision+2)^6+2
noncomputable def cutoffWorkPolynomial : Polynomial ℕ :=
  2*Polynomial.X+1 + 3*(6*(Polynomial.X+3)^4+4) + (2*(Polynomial.X+2)^2+1) + 3
noncomputable def currentWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  cutoffWorkPolynomial + CurrentGaussianBits.workPolynomial precision +
    (3*(2*(Polynomial.X+2)^2+1)+3) + primitiveWorkPolynomial (currentHeightPolynomial precision) + 4

theorem cutoffWorkPolynomial_eval (security : ℕ) : cutoffWorkPolynomial.eval security = cutoffWork security := by
  simp only [cutoffWorkPolynomial, cutoffWork, powerCounterWork, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  norm_num
  omega

theorem currentHeightPolynomial_eval (precision : Polynomial ℕ) (security : ℕ) :
    (currentHeightPolynomial precision).eval security = currentHeight security (precision.eval security) := by
  simp only [currentHeightPolynomial, currentHeight, CurrentGaussianBits.budget, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]

theorem currentWorkPolynomial_eval (precision : Polynomial ℕ) (security : ℕ) :
    (currentWorkPolynomial precision).eval security = currentWork security (precision.eval security) := by
  simp only [currentWorkPolynomial, cutoffWorkPolynomial, currentWork, cutoffWork, powerCounterWork,
    CurrentGaussianBits.workPolynomial_eval, primitiveWorkPolynomial_eval, currentHeightPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  norm_num
  omega

theorem current_polynomial_work (precision : Polynomial ℕ) (security : ℕ) :
    (current security (precision.eval security)).work ≤ (currentWorkPolynomial precision).eval security := by
  rw [currentWorkPolynomial_eval]
  exact (current_bounds security _).2

end CurrentAFT.BinaryActivationProgram

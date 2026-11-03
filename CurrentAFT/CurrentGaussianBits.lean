import CurrentAFT.WindowGaussianSampler
import AFT.BinaryWindowGaussian
import AFT.UnaryPolynomialCounters

/-! # Current Gaussian tables computed by Boolean-list arithmetic

The squared width is constructed by actual counter and binary encoding
programs. Every Gaussian series, rational normalization and array entry
is computed by the existing binary implementation. The cost is the
repository's explicit Boolean/list/counter work, not a TM compilation.
-/
namespace CurrentAFT.CurrentGaussianBits
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits Polynomial
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def widthCode (security : ℕ) : RationalResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let encoded := ofCounter square.count
  ⟨encoded.data, base.work + square.work + encoded.work + 3⟩

theorem widthCode_value (security : ℕ) : (widthCode security).data.decode = (security + 2 : ℚ)^2 := by
  simp only [widthCode, ofCounter_value, powerCounter_value, addCounter_value,
    Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]

def widthWork (security : ℕ) : ℕ :=
  2*security + 1 + powerCounterWork (security+2) 2 + 60*((security+2)^2+1)^2 + 3

theorem widthCode_work (security : ℕ) : (widthCode security).work ≤ widthWork security := by
  have hs := powerCounter_work (security+2) 2
  have he := ofCounter_work ((security+2)^2)
  simp only [widthCode, addCounter_value, powerCounter_value, addCounter_work, widthWork]
  omega

def table (security cutoff bits : ℕ) : ArrayResult (2*cutoff+1) :=
  let width := widthCode security
  let values := binaryWindowWeights width.data cutoff bits
  ⟨values.data, width.work + values.work + 2⟩

theorem table_value (security cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    ((table security cutoff bits).data.get index).decode =
      windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff bits index := by
  simp only [table, binaryWindowWeights_value, widthCode_value, WindowGaussianSampler.squaredWidth]

def budget (security bits : ℕ) : ℕ := (security+2)^2 + bits + 2

noncomputable section
open scoped Classical
attribute [local irreducible] widthCode table

theorem ratio_bounds (security cutoff : ℕ) (hcutoff : cutoff ≤ (security+2)^2) (point : Window cutoff) :
    0 ≤ gaussianRatio ((security+2 : ℚ)^2) point.val ∧
      gaussianRatio ((security+2 : ℚ)^2) point.val ≤ (security+2 : ℚ)^2 := by
  have hb : (0 : ℚ) < security+2 := by positivity
  have hp := Finset.mem_Icc.mp point.property
  have hlo : -(cutoff : ℚ) ≤ (point.val : ℚ) := by exact_mod_cast hp.1
  have hhi : (point.val : ℚ) ≤ (cutoff : ℚ) := by exact_mod_cast hp.2
  have hcut : (cutoff : ℚ) ≤ (security+2 : ℚ)^2 := by exact_mod_cast hcutoff
  have hproduct := mul_nonneg
    (show 0 ≤ (security+2 : ℚ)^2 + (point.val : ℚ) by linarith)
    (show 0 ≤ (security+2 : ℚ)^2 - (point.val : ℚ) by linarith)
  unfold gaussianRatio
  refine ⟨div_nonneg (sq_nonneg _) (pow_pos hb _).le, ?_⟩
  apply (div_le_iff₀ (pow_pos hb _)).mpr
  nlinarith only [hproduct]

theorem ratio_height (security cutoff bits : ℕ) (hcutoff : cutoff ≤ (security+2)^2) (point : Window cutoff) :
    HeightBound (gaussianRatio ((security+2 : ℚ)^2) point.val) (3*budget security bits) := by
  have hp := Finset.mem_Icc.mp point.property
  have habs : point.val.natAbs ≤ (security+2)^2 := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    have hpoint : |point.val| ≤ (cutoff : ℤ) := abs_le.mpr hp
    exact hpoint.trans (Nat.cast_le.mpr hcutoff)
  have hpoint := HeightBound.of_int (habs.trans (Nat.lt_two_pow_self (n := (security+2)^2)).le)
  have hwidth := HeightBound.nat_coarse ((security+2)^2)
  have hratio := (hpoint.pow 2).div hwidth
  change HeightBound ((point.val : ℚ)^2 / ((security+2)^2 : ℕ)) _ at hratio
  have hratio' : HeightBound (gaussianRatio ((security+2 : ℚ)^2) point.val) (3*(security+2)^2) := by
    convert hratio using 1 <;> norm_num [gaussianRatio, Nat.cast_add, Nat.cast_pow]
    omega
  exact hratio'.mono (by unfold budget; omega)

theorem input_bounds (security cutoff bits : ℕ) (hcutoff : cutoff ≤ (security+2)^2) :
    2 ≤ budget security bits ∧ cutoff ≤ budget security bits ∧ bits ≤ budget security bits ∧
      HeightBound (widthCode security).data.decode (budget security bits) ∧
      (∀ point : Window cutoff, 0 ≤ gaussianRatio (widthCode security).data.decode point.val ∧
        gaussianRatio (widthCode security).data.decode point.val ≤ budget security bits) ∧
      (∀ point : Window cutoff, HeightBound (gaussianRatio (widthCode security).data.decode point.val)
        (3*budget security bits)) := by
  have hb : 2 ≤ budget security bits := by unfold budget; omega
  have hc : cutoff ≤ budget security bits := by unfold budget; omega
  have hi : bits ≤ budget security bits := by unfold budget; omega
  have hw : HeightBound (widthCode security).data.decode (budget security bits) := by
    rw [widthCode_value]
    have h := HeightBound.nat_coarse ((security+2)^2)
    have h' : HeightBound ((security+2 : ℚ)^2) ((security+2)^2) := by exact_mod_cast h
    exact h'.mono (by unfold budget; omega)
  have hr (point : Window cutoff) : 0 ≤ gaussianRatio (widthCode security).data.decode point.val ∧
      gaussianRatio (widthCode security).data.decode point.val ≤ budget security bits := by
    rw [widthCode_value]
    have h := ratio_bounds security cutoff hcutoff point
    refine ⟨h.1, h.2.trans ?_⟩
    exact_mod_cast (show (security+2)^2 ≤ budget security bits by unfold budget; omega)
  have hh (point : Window cutoff) : HeightBound (gaussianRatio (widthCode security).data.decode point.val)
      (3*budget security bits) := by
    rw [widthCode_value]
    exact ratio_height security cutoff bits hcutoff point
  exact ⟨hb, hc, hi, hw, hr, hh⟩

def tableWork (security bits : ℕ) : ℕ := widthWork security + binaryWindowWork (budget security bits) + 2

theorem table_work (security cutoff bits : ℕ) (hcutoff : cutoff ≤ (security+2)^2) :
    (table security cutoff bits).work ≤ tableWork security bits := by
  rcases input_bounds security cutoff bits hcutoff with ⟨hb, hc, hi, hw, hr, hh⟩
  have ht := binaryWindowWeights_work (widthCode security).data cutoff bits (budget security bits) hb hc hi hw hr hh
  have hwc := widthCode_work security
  unfold table tableWork
  dsimp only
  omega

theorem table_height (security cutoff bits : ℕ) (hcutoff : cutoff ≤ (security+2)^2)
    (index : Fin (2*cutoff+1)) :
    HeightBound ((table security cutoff bits).data.get index).decode (500000000*(budget security bits)^6) := by
  rcases input_bounds security cutoff bits hcutoff with ⟨hb, hc, hi, _hw, hr, hh⟩
  unfold table
  exact binaryWindowWeights_height (widthCode security).data cutoff bits (budget security bits) hb hc hi hr hh index

theorem table_entry_lengths (security cutoff bits : ℕ) (hcutoff : cutoff ≤ (security+2)^2)
    (index : Fin (2*cutoff+1)) :
    ((table security cutoff bits).data.get index).numerator.length ≤ 500000000*(budget security bits)^6+1 ∧
      ((table security cutoff bits).data.get index).denominator.length ≤ 500000000*(budget security bits)^6+1 :=
  RationalBits.lengths_of_height _ _ (table_height security cutoff bits hcutoff index)

noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  2*X + 1 + 3*(6*(X+3)^4+4) + 60*((X+2)^2+1)^2 + 3 +
    binaryWindowPolynomial ((X+2)^2+precision+2) + 2

theorem workPolynomial_eval (precision : Polynomial ℕ) (security : ℕ) :
    (workPolynomial precision).eval security = tableWork security (precision.eval security) := by
  simp only [workPolynomial, tableWork, widthWork, budget, binaryWindowPolynomial_eval,
    powerCounterWork, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  norm_num
  ring

theorem table_polynomial_work (precision : Polynomial ℕ) (security cutoff : ℕ)
    (hcutoff : cutoff ≤ (security+2)^2) :
    (table security cutoff (precision.eval security)).work ≤ (workPolynomial precision).eval security := by
  rw [workPolynomial_eval]
  exact table_work security cutoff _ hcutoff

end
end CurrentAFT.CurrentGaussianBits

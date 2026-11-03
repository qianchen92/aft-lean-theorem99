import AFT.TaggedFock

/-! # All degrees of a genuine finite tagged polynomial -/

namespace AFT.TaggedFock

open MeasureTheory TensorFock NonlinearFock
open scoped BigOperators Classical

variable {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]

/-- A finite complex sum has its actual squared norm bounded by the number
of terms times their squared norms. -/
theorem normSq_sum_le_card_sum {Term : Type*} (terms : Finset Term) (value : Term → ℂ) :
    Complex.normSq (∑ term ∈ terms, value term) ≤
      (terms.card : ℝ) * ∑ term ∈ terms, Complex.normSq (value term) := by
  have hr := Finset.sum_mul_sq_le_sq_mul_sq terms (fun _ => (1 : ℝ)) (fun term => (value term).re)
  have hi := Finset.sum_mul_sq_le_sq_mul_sq terms (fun _ => (1 : ℝ)) (fun term => (value term).im)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hr hi
  simp only [Complex.normSq_apply, Complex.re_sum, Complex.im_sum, Finset.sum_add_distrib, ← pow_two]
  nlinarith

/-- Fixed-degree multiplication costs only the complete finite tagged
coefficient energy. Every tagged degree, including the marked fourth degree,
is included in the actual polynomial. -/
theorem polynomial_cubic_block_energy_le [Nonempty Coordinate] (degrees : Finset ℕ)
    (tagged : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate)
    (linear : Index → Coordinate → ℝ)
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (capacity : ℕ)
    (hcapacity : (SelectionBound.nonlinearSupport
      (fun index word => (Real.sqrt 2) ^ 2 * quadratic index word)
      (fun index word => (Real.sqrt 2) ^ 3 * cubic index word)).card ≤ capacity)
    (henergy : (∑ index, ∑ coordinate, (Real.sqrt 2 * linear index coordinate) ^ 2) ≤ 1 / 8)
    (hsmall : (∑ index, (128 * SelectionBound.localPairNorm
      (fun index word => (Real.sqrt 2) ^ 2 * quadratic index word) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (fun index word => (Real.sqrt 2) ^ 3 * cubic index word) index)) ≤ 1 / 2) :
    (∫ value, Complex.normSq (seriesEvaluation degrees tagged value *
      cubicBlockProduct linear quadratic cubic value) ∂FockGaussian.field) ≤
      ((degrees.card : ℝ) * ∑ degree ∈ degrees,
        (degree.factorial : ℝ) * 2 ^ degree * BlockFock.tensorEnergy (tagged degree)) *
          (16 * Real.exp (8 * ∑ coordinate, (∑ index, Real.sqrt 2 * linear index coordinate) ^ 2)) := by
  let function (degree : ℕ) (value : Coordinate → ℂ) :=
    tensorEvaluation (tagged degree) value * cubicBlockProduct linear quadratic cubic value
  have hmem (degree : ℕ) : MemLp (function degree) 2 FockGaussian.field :=
    (homogeneous_times_polynomial (tagged degree) (cubicBlockProduct_polynomial linear quadratic cubic)).memLp
  have hint (degree : ℕ) : Integrable (fun value => Complex.normSq (function degree value)) FockGaussian.field := by
    simpa only [← Complex.sq_norm] using (memLp_two_iff_integrable_sq_norm (hmem degree).aestronglyMeasurable).mp (hmem degree)
  have hsum : MemLp (fun value => ∑ degree ∈ degrees, function degree value) 2 FockGaussian.field :=
    memLp_finset_sum _ (fun degree _ => hmem degree)
  have hleft : Integrable (fun value => Complex.normSq (∑ degree ∈ degrees, function degree value)) FockGaussian.field := by
    simpa only [← Complex.sq_norm] using (memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).mp hsum
  have hright := (integrable_finset_sum degrees (fun degree _ => hint degree)).const_mul (degrees.card : ℝ)
  have hpoint (value : Coordinate → ℂ) :
      seriesEvaluation degrees tagged value * cubicBlockProduct linear quadratic cubic value =
        ∑ degree ∈ degrees, function degree value := by
    simp only [seriesEvaluation, Finset.sum_mul, function]
  simp_rw [hpoint]
  calc
    _ ≤ ∫ value, (degrees.card : ℝ) * ∑ degree ∈ degrees, Complex.normSq (function degree value) ∂FockGaussian.field :=
      integral_mono hleft hright (fun value => normSq_sum_le_card_sum degrees (fun degree => function degree value))
    _ = (degrees.card : ℝ) * ∑ degree ∈ degrees,
        ∫ value, Complex.normSq (function degree value) ∂FockGaussian.field := by
      rw [MeasureTheory.integral_const_mul (degrees.card : ℝ), integral_finset_sum _ (fun degree _ => hint degree)]
    _ ≤ (degrees.card : ℝ) * ∑ degree ∈ degrees,
        ((degree.factorial : ℝ) * 2 ^ degree * BlockFock.tensorEnergy (tagged degree)) *
          (16 * Real.exp (8 * ∑ coordinate, (∑ index, Real.sqrt 2 * linear index coordinate) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro degree _
      simpa only [Fintype.card_fin] using tagged_cubic_block_energy_le (tagged degree) linear quadratic cubic
        capacity hcapacity henergy hsmall
    _ = _ := by rw [← Finset.sum_mul]; ring

end AFT.TaggedFock

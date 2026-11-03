import AFT.LocalResponse

/-!
# Finite mixed-fiber cost of a partial matrix operator

An arbitrary finite alphabet `κ` packages the other integrated coordinates;
its weight may be any nonnegative product weight. Thus the estimates apply
to every mixed fiber after any chosen set of the other coordinates is fixed.
The additional penalty for fixing this output coordinate is derived below.
-/

namespace AFT

open scoped BigOperators

section PartialMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A coordinate operator on densities, given by its actual finite matrix. -/
noncomputable def densityMatrixApply (matrix : ι → ι → ℝ) (density : ι → ℝ) : ι → ℝ :=
  fun output => ∑ input, matrix output input * density input

/-- Apply the density matrix to one coordinate of a joint kernel. -/
noncomputable def partialDensityMatrix (matrix : ι → ι → ℝ) (kernel : ι → κ → ℝ) : ι → κ → ℝ :=
  fun output remaining => densityMatrixApply matrix (fun input => kernel input remaining) output

/-- Integrated norm of the coordinate and any remaining coordinates. -/
noncomputable def integratedFiberNorm (primary : ι → ℝ) (remaining : κ → ℝ)
    (kernel : ι → κ → ℝ) : ℝ :=
  Real.sqrt (∑ rest, remaining rest * ∑ color, primary color * kernel color rest ^ 2)

/-- Largest remaining-coordinate L2 fiber after fixing the distinguished
coordinate. This uses the ordinary finite-function supremum norm. -/
noncomputable def fixedFiberNorm (remaining : κ → ℝ) (kernel : ι → κ → ℝ) : ℝ :=
  ‖fun color => Real.sqrt (∑ rest, remaining rest * kernel color rest ^ 2)‖

/-- The two terms in mixed activity that differ only by fixing this
coordinate. `rate = 1 / sqrt(pool)` is the normalization for this pool. -/
noncomputable def coordinateActivity (rate : ℝ) (primary : ι → ℝ) (remaining : κ → ℝ)
    (kernel : ι → κ → ℝ) : ℝ :=
  rate * integratedFiberNorm primary remaining kernel + rate ^ 2 * fixedFiberNorm remaining kernel

omit [Fintype κ] in
/-- The exact finite weighted row Cauchy--Schwarz inequality. -/
theorem densityMatrixApply_sq_le (matrix : ι → ι → ℝ) (primary density : ι → ℝ)
    (hp : ∀ color, 0 < primary color) (output : ι) :
    densityMatrixApply matrix density output ^ 2 ≤
      (∑ input, matrix output input ^ 2 / primary input) *
        ∑ input, primary input * density input ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro color _
    exact div_nonneg (sq_nonneg _) (le_of_lt (hp color))
  · intro color _
    exact mul_nonneg (le_of_lt (hp color)) (sq_nonneg _)
  · intro color _
    have hn := ne_of_gt (hp color)
    field_simp

/-- Finite Hilbert-valued extension of the L2 operator estimate, proved by
summing the actual scalar quadratic inequality over remaining coordinates. -/
theorem partialDensityMatrix_integrated_le (matrix : ι → ι → ℝ)
    (primary : ι → ℝ) (remaining : κ → ℝ) (kernel : ι → κ → ℝ) (bound : ℝ)
    (hq : ∀ rest, 0 ≤ remaining rest)
    (hb : 0 ≤ bound)
    (hoperator : ∀ density : ι → ℝ,
      (∑ output, primary output * densityMatrixApply matrix density output ^ 2) ≤
        bound ^ 2 * ∑ input, primary input * density input ^ 2) :
    integratedFiberNorm primary remaining (partialDensityMatrix matrix kernel) ≤
      bound * integratedFiberNorm primary remaining kernel := by
  have hsum : (∑ rest, remaining rest *
      ∑ color, primary color * partialDensityMatrix matrix kernel color rest ^ 2) ≤
      bound ^ 2 * ∑ rest, remaining rest * ∑ color, primary color * kernel color rest ^ 2 := by
    calc
      _ ≤ ∑ rest, remaining rest *
          (bound ^ 2 * ∑ color, primary color * kernel color rest ^ 2) := by
        apply Finset.sum_le_sum
        intro rest _
        exact mul_le_mul_of_nonneg_left (hoperator (fun color => kernel color rest)) (hq rest)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro rest _
        ring
  unfold integratedFiberNorm
  calc
    _ ≤ Real.sqrt (bound ^ 2 * ∑ rest, remaining rest *
        ∑ color, primary color * kernel color rest ^ 2) := Real.sqrt_le_sqrt hsum
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg bound), Real.sqrt_sq hb]

/-- A fixed output consumes the old integrated input fiber. The weighted
row norm is the genuine finite L2-to-supremum operator norm bound. -/
theorem partialDensityMatrix_fixed_le (matrix : ι → ι → ℝ)
    (primary : ι → ℝ) (remaining : κ → ℝ) (kernel : ι → κ → ℝ) (bound : ℝ)
    (hp : ∀ color, 0 < primary color) (hq : ∀ rest, 0 ≤ remaining rest)
    (hb : 0 ≤ bound)
    (hrow : ∀ output, (∑ input, matrix output input ^ 2 / primary input) ≤ bound ^ 2) :
    fixedFiberNorm remaining (partialDensityMatrix matrix kernel) ≤
      bound * integratedFiberNorm primary remaining kernel := by
  unfold fixedFiberNorm
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (Real.sqrt_nonneg _))).mpr
  intro output
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsum : (∑ rest, remaining rest * partialDensityMatrix matrix kernel output rest ^ 2) ≤
      bound ^ 2 * ∑ rest, remaining rest * ∑ color, primary color * kernel color rest ^ 2 := by
    calc
      _ ≤ ∑ rest, remaining rest *
          (bound ^ 2 * ∑ color, primary color * kernel color rest ^ 2) := by
        apply Finset.sum_le_sum
        intro rest _
        apply mul_le_mul_of_nonneg_left _ (hq rest)
        exact (densityMatrixApply_sq_le matrix primary (fun color => kernel color rest) hp output).trans
          (mul_le_mul_of_nonneg_right (hrow output)
            (Finset.sum_nonneg fun color _ => mul_nonneg (le_of_lt (hp color)) (sq_nonneg _)))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro rest _
        ring
  calc
    _ ≤ Real.sqrt (bound ^ 2 * ∑ rest, remaining rest *
        ∑ color, primary color * kernel color rest ^ 2) := Real.sqrt_le_sqrt hsum
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg bound), Real.sqrt_sq hb]

/-- The mixed-fiber cost is `C₂ + rate * C∞`, without a palette-size
constant. Setting `rate = 1 / sqrt(pool)` gives the V7 bound. -/
theorem partialDensityMatrix_activity_le (matrix : ι → ι → ℝ)
    (primary : ι → ℝ) (remaining : κ → ℝ) (kernel : ι → κ → ℝ)
    (rate bound₂ boundSup : ℝ) (hrate : 0 ≤ rate)
    (hp : ∀ color, 0 < primary color) (hq : ∀ rest, 0 ≤ remaining rest)
    (hb₂ : 0 ≤ bound₂) (hbSup : 0 ≤ boundSup)
    (hoperator : ∀ density : ι → ℝ,
      (∑ output, primary output * densityMatrixApply matrix density output ^ 2) ≤
        bound₂ ^ 2 * ∑ input, primary input * density input ^ 2)
    (hrow : ∀ output, (∑ input, matrix output input ^ 2 / primary input) ≤ boundSup ^ 2) :
    coordinateActivity rate primary remaining (partialDensityMatrix matrix kernel) ≤
      (bound₂ + rate * boundSup) * coordinateActivity rate primary remaining kernel := by
  have hi := partialDensityMatrix_integrated_le matrix primary remaining kernel bound₂
    hq hb₂ hoperator
  have hf := partialDensityMatrix_fixed_le matrix primary remaining kernel boundSup hp hq hbSup hrow
  have hn : 0 ≤ fixedFiberNorm remaining kernel := norm_nonneg _
  unfold coordinateActivity
  have hcoeff : 0 ≤ bound₂ + rate * boundSup := by positivity
  calc
    _ ≤ rate * (bound₂ * integratedFiberNorm primary remaining kernel) +
        rate ^ 2 * (boundSup * integratedFiberNorm primary remaining kernel) :=
      add_le_add (mul_le_mul_of_nonneg_left hi hrate)
        (mul_le_mul_of_nonneg_left hf (sq_nonneg rate))
    _ ≤ _ := by nlinarith [mul_nonneg hcoeff (mul_nonneg (sq_nonneg rate) hn)]

/-- Summing over all configurations of the other fixed-coordinate set
preserves the same operator cost. The nonnegative `fiberWeight` can contain
both primary and body pool powers and the body analytic radius. -/
theorem partialDensityMatrix_mixed_sum_le {τ : Type*} [Fintype τ]
    (matrix : ι → ι → ℝ) (primary : ι → ℝ)
    (remaining : τ → κ → ℝ) (kernel : τ → ι → κ → ℝ)
    (fiberWeight : τ → ℝ) (rate bound₂ boundSup : ℝ)
    (hweight : ∀ fiber, 0 ≤ fiberWeight fiber) (hrate : 0 ≤ rate)
    (hp : ∀ color, 0 < primary color) (hq : ∀ fiber rest, 0 ≤ remaining fiber rest)
    (hb₂ : 0 ≤ bound₂) (hbSup : 0 ≤ boundSup)
    (hoperator : ∀ density : ι → ℝ,
      (∑ output, primary output * densityMatrixApply matrix density output ^ 2) ≤
        bound₂ ^ 2 * ∑ input, primary input * density input ^ 2)
    (hrow : ∀ output, (∑ input, matrix output input ^ 2 / primary input) ≤ boundSup ^ 2) :
    (∑ fiber, fiberWeight fiber * coordinateActivity rate primary (remaining fiber)
      (partialDensityMatrix matrix (kernel fiber))) ≤
      (bound₂ + rate * boundSup) * ∑ fiber, fiberWeight fiber *
        coordinateActivity rate primary (remaining fiber) (kernel fiber) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro fiber _
  have h := mul_le_mul_of_nonneg_left
    (partialDensityMatrix_activity_le matrix primary (remaining fiber) (kernel fiber)
      rate bound₂ boundSup hrate hp (hq fiber) hb₂ hbSup hoperator hrow) (hweight fiber)
  nlinarith only [h]

end PartialMatrix

end AFT

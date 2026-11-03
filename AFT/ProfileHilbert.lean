import AFT.FirstCoefficientFormula
import AFT.ConditionalMeanFock

/-! # Exact Hilbert vectors of physical color profiles -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

namespace FiniteConcentration

variable {Sample Hilbert : Type*} [Fintype Sample]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

theorem vectorMean_norm_le (law : FiniteDist Sample) (value : Sample → Hilbert)
    (bound : ℝ) (hvalue : ∀ sample, ‖value sample‖ ≤ bound) : ‖vectorMean law value‖ ≤ bound := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ sample, law.weight sample * bound := by
      apply Finset.sum_le_sum
      intro sample _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (law.nonneg sample)]
      exact mul_le_mul_of_nonneg_left (hvalue sample) (law.nonneg sample)
    _ = _ := by rw [← Finset.sum_mul, law.sum_one, one_mul]

theorem vectorMean_centered (law : FiniteDist Sample) (value : Sample → Hilbert) :
    vectorMean law (fun sample => value sample - vectorMean law value) = 0 := by
  simp only [vectorMean, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, law.sum_one, one_smul, sub_self]

theorem centered_value_norm_le (law : FiniteDist Sample) (value : Sample → Hilbert)
    (bound : ℝ) (hvalue : ∀ sample, ‖value sample‖ ≤ bound) (sample : Sample) :
    ‖value sample - vectorMean law value‖ ≤ 2 * bound := by
  exact (norm_sub_le _ _).trans (by linarith [hvalue sample, vectorMean_norm_le law value bound hvalue])

end FiniteConcentration

namespace ProfileHilbert

variable {Color Sample : Type*} [Fintype Color] [Fintype Sample]

/-- Whitening is a literal linear map into the finite Euclidean space. -/
def whiten (reference : Color → ℝ) : (Color → ℝ) →ₗ[ℝ] EuclideanSpace ℝ Color where
  toFun profile := WithLp.toLp 2 (fun color => profile color / Real.sqrt (reference color))
  map_add' first second := by ext color; simp [add_div]
  map_smul' scalar profile := by ext color; simp [mul_div_assoc]

omit [Fintype Sample] in
@[simp] theorem whiten_apply (reference profile : Color → ℝ) (color : Color) :
    (whiten reference profile).ofLp color = profile color / Real.sqrt (reference color) := rfl

omit [Fintype Sample] in
/-- Its norm is precisely the weighted profile energy. -/
theorem whiten_norm_sq (reference profile : Color → ℝ) (href : ∀ color, 0 ≤ reference color) :
    ‖whiten reference profile‖ ^ 2 = profileSquareNorm reference profile := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [whiten_apply, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (href _)]
  rfl

/-- Averaging arbitrary joint-source profile vectors retains their Hilbert
bound without a palette-cardinality factor. -/
theorem whiten_average (reference : Color → ℝ) (law : FiniteDist Sample) (profile : Sample → Color → ℝ) :
    whiten reference (fun color => law.expectation (fun sample => profile sample color)) =
      FiniteConcentration.vectorMean law (fun sample => whiten reference (profile sample)) := by
  have hh : (fun color => law.expectation (fun sample => profile sample color)) =
      ∑ sample, law.weight sample • profile sample := by
    funext color
    simp only [FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hh, map_sum]
  simp only [map_smul, FiniteConcentration.vectorMean]

/-- Centered mixture profiles are the exact average of the centered
component vectors. -/
theorem whiten_mixture_centered (reference : FiniteDist Color) (law : FiniteDist Sample)
    (component : Sample → FiniteDist Color) :
    whiten reference.weight (fun color => (law.mix component).weight color - reference.weight color) =
      FiniteConcentration.vectorMean law (fun sample => whiten reference.weight
        (fun color => (component sample).weight color - reference.weight color)) := by
  rw [← whiten_average]
  congr 1
  funext color
  simp only [FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    law.sum_one, one_mul, FiniteDist.mix_weight]

end ProfileHilbert

end

end AFT

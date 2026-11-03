import AFT.RationalWindowGaussian
import AFT.ActualRootNumericalStability

/-! # The root Gaussian is supplied by a proved rational program -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram FiniteDist
open scoped BigOperators

/-- The actual squared root width is rational and requires no square-root oracle. -/
def actualRootSquaredWidth (n : ℕ) : ℚ := 8*(n : ℚ)^2

def actualRootGaussianWeights (n bits : ℕ) (index : Fin (2*(3*n^2-1)+1)) : ℚ :=
  windowApproxWeight (actualRootSquaredWidth n) (3*n^2-1) bits (windowIndexEquiv _ index)

/-- Exact rational dynamic programming with a computed approximation of the
actual scalar weights. The array is materialized at every population step. -/
def actualRootGaussianProbability (n bits count : ℕ) (target : ℤ) : ℚ :=
  integerLookup (run (2*(3*n^2-1)) (actualRootGaussianWeights n bits) count).data
    ((3*n^2-1)*count) target

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance actualRootGaussianProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualRootGaussianLaw (n bits : ℕ) : FiniteDist (Window (v7RootCutoff n)) :=
  windowApproxLaw (actualRootSquaredWidth n) (v7RootCutoff n) bits

theorem actualRootSquaredWidth_positive (n : ℕ) (hn : 0 < n) : 0 < actualRootSquaredWidth n := by
  unfold actualRootSquaredWidth
  positivity

theorem actualRootGaussianLaw_l1 (n bits : ℕ) (hn : 0 < n) :
    (∑ point,|(actualRootGaussianLaw n bits).weight point-
      (windowGaussian (v7RootWidth n) (v7RootCutoff n)).weight point|) ≤ 1/(2 : ℝ)^bits := by
  apply windowApproxLaw_l1 (actualRootSquaredWidth n) (v7RootWidth n) (v7RootCutoff n) bits
    (actualRootSquaredWidth_positive n hn)
  simp only [actualRootSquaredWidth,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast,v7RootWidth_sq]

theorem actualRootGaussianProbability_exact (n bits count : ℕ) (target : ℤ) :
    (actualRootGaussianProbability n bits count target : ℝ)=
      RootSlice.sumProbability (actualRootGaussianLaw n bits) (fun point => (point : ℤ)) count target := by
  rw [← integerLookup_run_probability]
  change ((integerLookup (run (2*(3*n^2-1)) (actualRootGaussianWeights n bits) count).data
      ((3*n^2-1)*count) target : ℚ) : ℝ)=
    integerLookup (run (2*(3*n^2-1)) (fun index => (actualRootGaussianWeights n bits index : ℝ)) count).data
      ((3*n^2-1)*count) target
  unfold integerLookup
  split_ifs
  · exact run_rat_cast _ _ _ _
  · simp only [Rat.cast_zero]

/-- The exact computed convolution has a uniform error bound at every integer
query; the claim contains no numerical weight approximation hypothesis. -/
theorem actualRootGaussianProbability_error (n bits count : ℕ) (target : ℤ) (hn : 0 < n) :
    |(actualRootGaussianProbability n bits count target : ℝ)-
      RootSlice.sumProbability (windowGaussian (v7RootWidth n) (v7RootCutoff n))
        (fun point => (point : ℤ)) count target| ≤ (count : ℝ)/(2 : ℝ)^bits := by
  rw [actualRootGaussianProbability_exact]
  have hh := RootSlice.sumProbability_l1_error (actualRootGaussianLaw n bits)
    (windowGaussian (v7RootWidth n) (v7RootCutoff n)) (fun point => (point : ℤ)) count target
  exact hh.trans (by simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (actualRootGaussianLaw_l1 n bits hn) (Nat.cast_nonneg count))

/-- The numerical scalar program approximates the full actual zero-sum root
law with negligible error; all scalar numerical premises are discharged. -/
theorem actual_root_gaussian_program_conditioning_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ hpos : 0 < RootSlice.sumProbability (actualRootGaussianLaw n n)
          (fun point => (point : ℤ)) (Parameters.bodies n) 0,
        TVBound (RootSlice.law (fun _ : Fin (Parameters.bodies n) => actualRootGaussianLaw n n)
          (fun point => (point : ℤ)) 0 hpos)
          (RootSlice.law (fun _ : Fin (Parameters.bodies n) => windowGaussian (v7RootWidth n) (v7RootCutoff n))
            (fun point => (point : ℤ)) 0 (window_root_probability_positive _ _ _))
          (actualRootNumericalError n) := by
  filter_upwards [actual_root_numerical_conditioning_eventually,Filter.eventually_ge_atTop 1] with n hh hn
  exact hh (actualRootGaussianLaw n n) (actualRootGaussianLaw_l1 n n hn)

end
end AFT.V7Calibration

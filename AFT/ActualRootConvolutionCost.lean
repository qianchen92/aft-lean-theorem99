import AFT.RootConvolutionProgram
import AFT.RootErrorParameters

/-! # Polynomial convolution-array bounds for the actual V7 root parameters -/
namespace AFT.V7Calibration
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

/-- This executable rational program uses the literal V7 clipped support.
Only the supplied scalar weights require a numerical Gaussian evaluator. -/
def actualRootConvolution (n : ℕ) (weight : Fin (2*(3*n^2-1)+1) → ℚ)
    (count : ℕ) : Result ℚ :=
  run (2*(3*n^2-1)) weight count

noncomputable section

/-- All needed remaining-population sums fit in one row of polynomial
length, including `N`, `N-1`, and `N-k` for every selected order. -/
theorem actual_root_convolution_size_work {R : Type*} [Semiring R]
    (n : ℕ) (hn : 2 ≤ n) (weight : Fin (2*v7RootCutoff n+1) → R)
    (count : ℕ) (hcount : count ≤ Parameters.bodies n) :
    (run (2*v7RootCutoff n) weight count).data.size ≤ 13*n^62 ∧
      (run (2*v7RootCutoff n) weight count).work ≤ 1275*n^124 := by
  have hn1 : 1 ≤ n := by omega
  have hp2 : 1 ≤ n^2 := Nat.one_le_pow _ _ hn1
  have hp62 : 1 ≤ n^62 := Nat.one_le_pow _ _ hn1
  have hp124 : 1 ≤ n^124 := Nat.one_le_pow _ _ hn1
  have hcut : 2*v7RootCutoff n ≤ 6*n^2 := by unfold v7RootCutoff; omega
  have hN : count ≤ 2*n^60 := by
    apply hcount.trans
    apply (Nat.sub_le _ _).trans
    simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  have hspan : (2*v7RootCutoff n)*count+1 ≤ 13*n^62 := by
    have hh := Nat.mul_le_mul hcut hN
    have he : (6*n^2)*(2*n^60)=12*n^62 := by
      rw [show n^62=n^2*n^60 by rw [← pow_add]]
      ring
    rw [he] at hh
    omega
  have halphabet : 2*v7RootCutoff n+1 ≤ 7*n^2 := by omega
  refine ⟨by rw [run_size]; exact hspan,?_⟩
  apply (run_work_le _ _ _).trans
  calc
    _ ≤ 1+7*(2*n^60)*(13*n^62)*(7*n^2) := by gcongr
    _ = 1+1274*n^124 := by
      rw [show n^124=n^60*n^62*n^2 by rw [← pow_add,← pow_add]]
      ring
    _ ≤ _ := by omega

theorem actualRootConvolution_size_work (n : ℕ) (hn : 2 ≤ n)
    (weight : Fin (2*(3*n^2-1)+1) → ℚ) (count : ℕ)
    (hcount : count ≤ Parameters.bodies n) :
    (actualRootConvolution n weight count).data.size ≤ 13*n^62 ∧
      (actualRootConvolution n weight count).work ≤ 1275*n^124 :=
  actual_root_convolution_size_work n hn weight count hcount

/-- Instantiation at the same Gaussian weights used by the actual protected
root law. This identifies the calculation, independently of its precision. -/
theorem actual_root_probability_program (n count : ℕ) (target : ℤ) :
    integerLookup (run (2*v7RootCutoff n)
      (fun index => (windowGaussian (v7RootWidth n) (v7RootCutoff n)).weight
        (windowIndexEquiv (v7RootCutoff n) index)) count).data
      (v7RootCutoff n*count) target=
      RootSlice.sumProbability (windowGaussian (v7RootWidth n) (v7RootCutoff n))
        (fun point => (point : ℤ)) count target :=
  integerLookup_run_gaussian _ _ _ _

end
end AFT.V7Calibration

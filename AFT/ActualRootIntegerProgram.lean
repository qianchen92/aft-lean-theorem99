import AFT.ActualRootConvolutionCost
import AFT.IntegerConvolutionBounds

/-! # Actual integer-ticket root convolution with polynomial binary lengths -/
namespace AFT.V7Calibration
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

/-- No rational reduction is performed within the convolution. The complete
integer numerator is divided by the common ticket denominator at the end. -/
def actualRootIntegerConvolution (n : ℕ) (counts : Fin (2*(3*n^2-1)+1) → ℕ)
    (count : ℕ) : Result ℕ :=
  run (2*(3*n^2-1)) counts count

noncomputable section

/-- Work, row size, numerator size, and denominator size are all explicit
for the actual population, including the largest root normalizer query. -/
theorem actual_root_integer_program_bounds (n : ℕ) (hn : 2 ≤ n)
    (counts : Fin (2*(3*n^2-1)+1) → ℕ) (bits : ℕ)
    (htotal : ∑ source,counts source=2^bits) (count target : ℕ)
    (hcount : count ≤ Parameters.bodies n) :
    (actualRootIntegerConvolution n counts count).data.size ≤ 13*n^62 ∧
      (actualRootIntegerConvolution n counts count).work ≤ 1275*n^124 ∧
      (lookup (actualRootIntegerConvolution n counts count).data target).size ≤ 2*bits*n^60+1 ∧
      (2^(bits*count)).size ≤ 2*bits*n^60+1 := by
  have hN : count ≤ 2*n^60 := by
    apply hcount.trans
    apply (Nat.sub_le _ _).trans
    simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  have hs := actual_root_convolution_size_work n hn counts count hcount
  have hb := run_dyadic_size (2*(3*n^2-1)) counts bits htotal count target
  have hbound : bits*count+1 ≤ 2*bits*n^60+1 := by nlinarith
  refine ⟨hs.1,hs.2,hb.trans hbound,?_⟩
  simpa only [Nat.size_pow] using hbound

/-- Every accumulation performed while producing the next row obeys the
same polynomial bit bound, not merely the final array value. -/
theorem actual_root_integer_accumulator_size (n : ℕ) (hn : 2 ≤ n)
    (counts : Fin (2*(3*n^2-1)+1) → ℕ) (bits : ℕ)
    (htotal : ∑ source,counts source=2^bits) (count target : ℕ)
    (hcount : count+1 ≤ Parameters.bodies n)
    (indices : Finset (Fin (2*(3*n^2-1)+1))) :
    (∑ source∈indices,rowTerm (2*(3*n^2-1)) counts count target source).size ≤ 2*bits*n^60+1 := by
  have hN : count+1 ≤ 2*n^60 := by
    apply hcount.trans
    apply (Nat.sub_le _ _).trans
    simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  apply (row_partial_dyadic_size (2*(3*n^2-1)) counts bits htotal count target indices).trans
  nlinarith

end
end AFT.V7Calibration

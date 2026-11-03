import AFT.ActualRootGaussianTickets

/-! # The complete executable integer Gaussian convolution and its actual error -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram FiniteDist
open scoped BigOperators

/-- Every scalar ticket count, including its Gaussian approximation, is
computed from `n`. No real-valued weight is an input to this program. -/
def actualRootTicketConvolution (n count : ℕ) : Result ℕ :=
  actualRootIntegerConvolution n (actualRootTicketCounts n n) count

def actualRootTicketProbability (n count : ℕ) (target : ℤ) : ℚ :=
  (integerLookup (actualRootTicketConvolution n count).data ((3*n^2-1)*count) target : ℕ)/
    (2 : ℚ)^(actualRootTicketBits n n*count)

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance actualRootTicketConvolutionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem actualRootTicketProbability_exact (n count : ℕ) (target : ℤ) :
    (actualRootTicketProbability n count target : ℝ)=
      RootSlice.sumProbability (actualRootTicketLaw n n) (fun point => (point : ℤ)) count target := by
  rw [← integerLookup_run_probability]
  have hweight : (fun index => (actualRootTicketLaw n n).weight (windowIndexEquiv (v7RootCutoff n) index))=
      fun index => (actualRootTicketCounts n n index : ℝ)/(2 : ℝ)^(actualRootTicketBits n n) := by
    funext index
    rw [actualRootTicketLaw_weight]
    simp only [v7RootCutoff,Equiv.symm_apply_apply]
  rw [hweight]
  unfold actualRootTicketProbability actualRootTicketConvolution actualRootIntegerConvolution
  push_cast
  rw [pow_mul]
  simp only [v7RootCutoff]
  unfold integerLookup
  split_ifs
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      run_nat_div (2*(3*n^2-1)) (actualRootTicketCounts n n) (2^(actualRootTicketBits n n)) count _
  · simp

theorem actualRootTicketProbability_error (n count : ℕ) (target : ℤ) (hn : 0 < n) :
    |(actualRootTicketProbability n count target : ℝ)-
      RootSlice.sumProbability (windowGaussian (v7RootWidth n) (v7RootCutoff n))
        (fun point => (point : ℤ)) count target| ≤ (count : ℝ)/(2 : ℝ)^n := by
  rw [actualRootTicketProbability_exact]
  have hh := RootSlice.sumProbability_l1_error (actualRootTicketLaw n n)
    (windowGaussian (v7RootWidth n) (v7RootCutoff n)) (fun point => (point : ℤ)) count target
  exact hh.trans (by simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (actualRootTicketLaw_l1 n n hn) (Nat.cast_nonneg count))

/-- The DP's real numerical inputs have disappeared. The computed ticket
rows and all arithmetic intermediates have explicit polynomial bounds. -/
theorem actualRootTicketConvolution_bounds (n count target : ℕ) (hn : 2 ≤ n)
    (hcount : count ≤ Parameters.bodies n) :
    (actualRootTicketConvolution n count).data.size ≤ 13*n^62 ∧
      (actualRootTicketConvolution n count).work ≤ 1275*n^124 ∧
      (lookup (actualRootTicketConvolution n count).data target).size ≤ 16*n^62+1 ∧
      (2^(actualRootTicketBits n n*count)).size ≤ 16*n^62+1 := by
  have hh := actual_root_integer_program_bounds n hn (actualRootTicketCounts n n)
    (actualRootTicketBits n n) (actualRootTicketCounts_sum n n) count target hcount
  have hb := actualRootTicketBits_bound n hn
  have hbound : 2*actualRootTicketBits n n*n^60+1 ≤ 16*n^62+1 := by
    calc
      _ ≤ 2*(8*n^2)*n^60+1 := by gcongr
      _ = _ := by rw [show n^62=n^2*n^60 by rw [← pow_add]]; ring
  exact ⟨hh.1,hh.2.1,hh.2.2.1.trans hbound,hh.2.2.2.trans hbound⟩

end
end AFT.V7Calibration

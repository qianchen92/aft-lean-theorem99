import AFT.RootConvolutionProgram

/-! # Integer-ticket convolution and bounds on every arithmetic intermediate -/
namespace AFT.FiniteConvolutionProgram
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The complete convolution coefficient cannot exceed the total number of
source tickets. This bound includes all impossible targets. -/
theorem run_nat_le_total (alphabet : ℕ) (counts : Fin (alphabet+1) → ℕ) (count target : ℕ) :
    lookup (run alphabet counts count).data target ≤ (∑ source,counts source)^count := by
  rw [run_correct]
  calc
    _ ≤ ∑ word : Fin count → Fin (alphabet+1),∏ i,counts (word i) := by
      apply Finset.sum_le_sum
      intro word _
      split_ifs <;> omega
    _ = _ := by
      rw [← Fintype.prod_sum]
      simp

/-- Exact rational normalization of the integer program; division occurs
only after the whole numerator has been computed. -/
theorem run_nat_div (alphabet : ℕ) (counts : Fin (alphabet+1) → ℕ)
    (tickets count target : ℕ) :
    ((lookup (run alphabet counts count).data target : ℕ) : ℝ)/(tickets : ℝ)^count=
      lookup (run alphabet (fun source => (counts source : ℝ)/(tickets : ℝ)) count).data target := by
  rw [run_correct,run_correct]
  unfold wordCoefficient
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr (by ext; simp)
  intro word _
  split_ifs
  · simp only [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  · simp

def rowTerm (alphabet : ℕ) (counts : Fin (alphabet+1) → ℕ)
    (count target : ℕ) (source : Fin (alphabet+1)) : ℕ :=
  if source.val ≤ target then counts source*lookup (run alphabet counts count).data (target-source.val) else 0

/-- Partial addition accumulators and every performed source product are
bounded by the next complete row mass. -/
theorem row_partial_le_total (alphabet : ℕ) (counts : Fin (alphabet+1) → ℕ)
    (count target : ℕ) (indices : Finset (Fin (alphabet+1))) :
    (∑ source∈indices,rowTerm alphabet counts count target source) ≤
      (∑ source,counts source)^(count+1) := by
  calc
    _ ≤ ∑ source,rowTerm alphabet counts count target source :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = lookup (run alphabet counts (count+1)).data target := by
      simp only [rowTerm,run_correct,wordCoefficient_succ]
    _ ≤ _ := run_nat_le_total alphabet counts (count+1) target

theorem row_term_le_total (alphabet : ℕ) (counts : Fin (alphabet+1) → ℕ)
    (count target : ℕ) (source : Fin (alphabet+1)) :
    rowTerm alphabet counts count target source ≤ (∑ source,counts source)^(count+1) := by
  simpa only [Finset.sum_singleton] using row_partial_le_total alphabet counts count target {source}

/-- With `bits` scalar bits, a row after `count` steps has at most
`bits*count+1` binary digits, even though its exact ticket denominator grows. -/
theorem run_dyadic_size (alphabet : ℕ) (counts : Fin (alphabet+1) → ℕ)
    (bits : ℕ) (htotal : ∑ source,counts source=2^bits) (count target : ℕ) :
    (lookup (run alphabet counts count).data target).size ≤ bits*count+1 := by
  have hh := run_nat_le_total alphabet counts count target
  rw [htotal,← pow_mul] at hh
  exact (Nat.size_le_size hh).trans_eq Nat.size_pow

theorem row_partial_dyadic_size (alphabet : ℕ) (counts : Fin (alphabet+1) → ℕ)
    (bits : ℕ) (htotal : ∑ source,counts source=2^bits) (count target : ℕ)
    (indices : Finset (Fin (alphabet+1))) :
    (∑ source∈indices,rowTerm alphabet counts count target source).size ≤ bits*(count+1)+1 := by
  have hh := row_partial_le_total alphabet counts count target indices
  rw [htotal,← pow_mul] at hh
  exact (Nat.size_le_size hh).trans_eq Nat.size_pow

end
end AFT.FiniteConvolutionProgram

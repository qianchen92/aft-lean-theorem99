import AFT.ActualReferenceProgram
import AFT.ActualPrimaryReciprocalProgram
import AFT.MixedReferenceCanonicalFibers

/-! # Executable centered output atoms with the actual primary denominator -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualReferenceAtomProgram (constant n : ℕ) (beta : ℚ) (input output : ℕ) : ℚ :=
  ((if input=output then 1 else 0)-actualReferenceProgram constant n beta output)*
    actualPrimaryReciprocalProgram constant n beta output

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance referenceAtomProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The centered numerator has absolute value at most one.  In particular
its numerical error is only the already controlled reciprocal error. -/
theorem actual_reference_atom_program_eventually (constant : ℕ) (hc : 1≤constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤(beta n : ℝ) ∧
      (beta n : ℝ)≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ input output : Fin (Parameters.modulus n),
      let atom := MixedKernel.referenceAtom (actualPrimaryLaw constant n (beta n))
        (actualReferenceLaw constant n (beta n)) input output
      |atom| ≤ 16*(n : ℝ)^40 ∧
      |(actualReferenceAtomProgram constant n (beta n) input.val output.val : ℝ)| ≤ 16*(n : ℝ)^40 ∧
      |(actualReferenceAtomProgram constant n (beta n) input.val output.val : ℝ)-atom| ≤
        actualPrimaryReciprocalProgramError n := by
  filter_upwards [actual_reference_program_eventually constant hc beta hbeta,
    actual_primary_reciprocal_program_eventually constant hc beta hbeta,
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    eventually_ge_atTop 2] with n href hinv hlower hn input output
  let r := (actualReferenceLaw constant n (beta n)).weight output
  have hr0 : 0≤r := (actualReferenceLaw constant n (beta n)).nonneg output
  have hr1 : r≤1 := by
    simpa only [(actualReferenceLaw constant n (beta n)).sum_one] using Finset.single_le_sum
      (fun color (_ : color∈Finset.univ) => (actualReferenceLaw constant n (beta n)).nonneg color)
      (Finset.mem_univ output)
  have hnum : |(if input=output then (1 : ℝ) else 0)-r|≤1 := by
    split_ifs <;> exact abs_le.mpr (by constructor <;> linarith)
  have hq0 : (0 : ℝ)<Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hp0 : 0<(actualPrimaryLaw constant n (beta n)).weight output :=
    lt_of_lt_of_le (by positivity) (hlower output)
  have hq : (Parameters.modulus n : ℝ)≤2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hpInv : |((actualPrimaryLaw constant n (beta n)).weight output)⁻¹|≤16*(n : ℝ)^40 := by
    rw [abs_of_pos (inv_pos.mpr hp0)]
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<1/(4*(Parameters.modulus n : ℝ))) (hlower output)
    simp only [one_div,inv_inv] at hh
    exact hh.trans (by nlinarith only [hq,pow_nonneg (show (0 : ℝ)≤n from Nat.cast_nonneg n) 40])
  have hprog : (actualReferenceAtomProgram constant n (beta n) input.val output.val : ℝ)=
      ((if input=output then 1 else 0)-r)*(actualPrimaryReciprocalProgram constant n (beta n) output.val : ℝ) := by
    unfold actualReferenceAtomProgram
    rw [Rat.cast_mul,Rat.cast_sub,href]
    congr 1
    by_cases hi : input=output
    · simp only [hi,if_true,Rat.cast_one,r]
    · have hv : input.val≠output.val := fun hh => hi (Fin.ext hh)
      simp only [hi,hv,if_false,Rat.cast_zero,r]
  dsimp only
  rw [MixedKernel.referenceAtom_eq,div_eq_mul_inv,hprog]
  refine ⟨?_,?_,?_⟩
  · rw [abs_mul]
    exact (mul_le_mul hnum hpInv (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · rw [abs_mul]
    have hh : |(actualPrimaryReciprocalProgram constant n (beta n) output.val : ℝ)|≤16*(n : ℝ)^40 := by
      rw [abs_of_pos (hinv output).1]
      exact (hinv output).2.1
    exact (mul_le_mul hnum hh (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · rw [←mul_sub,abs_mul]
    exact (mul_le_mul hnum (hinv output).2.2 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

end
end AFT.V7Calibration

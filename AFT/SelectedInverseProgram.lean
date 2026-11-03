import AFT.JointInverseMatrix
import AFT.ActualDensityInverseBounds
import AFT.NumericalSelectedCoefficient

/-! # Executable inverse of any selected local coefficient array -/
namespace AFT.RationalNumerics
open scoped BigOperators

def selectedInverseProgram (constant n : ℕ) (beta : ℚ) {colors slots : ℕ}
    (selected : Finset (Fin slots)) (kernel : (selected → Fin colors) → ℚ)
    (output : selected → Fin colors) : ℚ :=
  ∑ input,kernel input*∏ slot : selected,
    V7Calibration.actualDensityInverseProgram constant n beta (input slot).val (output slot).val

noncomputable section
open V7Calibration GaussianSource Filter MixedKernel
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000

/-- This is a finite palette loop on at most the selected coordinates;
all scalar inverse entries are supplied by the proved actual program. -/
theorem selected_inverse_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse constant n →
    ∀ (slots : ℕ) (selected : Finset (Fin slots)),
    ∀ (kernel : (selected → Fin (Parameters.modulus n)) → ℝ)
      (approximateKernel : (selected → Fin (Parameters.modulus n)) → ℚ),
    ∀ kernelBound kernelError : ℝ,0 ≤ kernelBound →0 ≤ kernelError →
    (∀ input,|kernel input| ≤ kernelBound) →
    (∀ input,|(approximateKernel input : ℝ)-kernel input| ≤ kernelError) →∀ output,
    |(selectedInverseProgram constant n (beta n) selected approximateKernel output : ℝ)-
      ∑ input,kernel input*∏ slot,actualDensityInverseEntry constant n (beta n) operator (input slot) (output slot)| ≤
      (Parameters.modulus n : ℝ)^selected.card*
        (kernelError+kernelBound*selected.card*actualDensityInverseProgramError n)*(257*(n : ℝ)^120)^selected.card := by
  filter_upwards [actual_density_inverse_estimates_eventually constant hc beta hbeta,eventually_ge_atTop 2]
    with n hi hn operator hop slots selected kernel approximateKernel kernelBound kernelError hb he hkernel happ output
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hbound : 1 ≤ 257*(n : ℝ)^120 := by have hh := one_le_pow₀ hn1 (n:=120);linarith
  have herr : 0 ≤ actualDensityInverseProgramError n := (abs_nonneg _).trans
    (hi operator hop ⟨0,(Parameters.modulus_prime n).pos⟩ ⟨0,(Parameters.modulus_prime n).pos⟩).2.2
  simp only [selectedInverseProgram,Rat.cast_sum,Rat.cast_mul,Rat.cast_prod]
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow] using
    finite_sum_product_perturbation kernel (fun input => (approximateKernel input : ℝ))
      (fun input slot => actualDensityInverseEntry constant n (beta n) operator (input slot) (output slot))
      (fun input slot => (actualDensityInverseProgram constant n (beta n) (input slot).val (output slot).val : ℝ))
      (257*(n : ℝ)^120) kernelBound (actualDensityInverseProgramError n) kernelError hbound hb herr he hkernel happ
      (fun input slot => (hi operator hop (input slot) (output slot)).1)
      (fun input slot => (hi operator hop (input slot) (output slot)).2.1)
      (fun input slot => (hi operator hop (input slot) (output slot)).2.2)

end
end AFT.RationalNumerics

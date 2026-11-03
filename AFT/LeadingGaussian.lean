import AFT.LeadingTensorActivity
import AFT.NonlinearFock

/-! # Low-degree Gaussian norm of actual literal leading outputs -/
namespace AFT.RepresentedPolynomial
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

def leadingGaussianValue (reference : Color → ℝ) (table : Table Color) (value : Color → ℂ) : ℂ :=
  MvPolynomial.eval₂ Complex.ofRealHom (fun color => value color/(Real.sqrt (reference color) : ℂ)) table

theorem leading_monomial_memLp (primary body : FiniteDist Color) (reference : Color → ℝ)
    (primaryChannel bodyChannel : Color → Color → ℝ) (powers : InputSeed Color →₀ ℕ) :
    MemLp (leadingGaussianValue reference
      (outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1))) 2 FockGaussian.field := by
  rw [← mixedMonomialSeed_output]
  have he : leadingGaussianValue reference (seedOutput primary body primaryChannel bodyChannel (mixedMonomialSeed powers))=
      TensorFock.tensorEvaluation (leadingSeedTensor primary body reference primaryChannel bodyChannel (mixedMonomialSeed powers)) := by
    funext value
    exact leadingSeedTensor_evaluation ..
  rw [he]
  exact NonlinearFock.tensor_memLp _

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open MeasureTheory GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem leadingActivityFactor_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ leadingActivityFactor n := by
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 0 ≤ responseEnergyConstant := by unfold responseEnergyConstant; positivity
  have hK : 1 ≤ Real.sqrt leadingEnergyConstant := Real.one_le_sqrt.mpr (by unfold leadingEnergyConstant; linarith)
  have hp : 1 ≤ (n : ℝ)^50 := one_le_pow₀ hx
  unfold leadingActivityFactor
  nlinarith

def leadingGaussianFactor (n cutoff : ℕ) : ℝ :=
  Real.sqrt (cutoff.factorial : ℝ)*leadingActivityFactor n^cutoff

theorem leadingGaussianFactor_nonneg (n cutoff : ℕ) : 0 ≤ leadingGaussianFactor n cutoff :=
  mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (leadingActivityFactor_nonneg n) _)

/-- Every literal monomial is handled as its original joint input tensor;
its output norm is independent of the number of its scalar tensor entries. -/
theorem actual_leading_monomial_energy_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ primaryPool bodyPool : ℕ,0<primaryPool →0<bodyPool →
    primaryPool ≤ Parameters.dimension n →bodyPool ≤ Parameters.dimension n →
    ∀ cutoff powers,weightedOrder (fun seed : InputSeed (Fin (Parameters.modulus n)) => seed.primaryOrder+seed.bodyOrder) powers ≤ cutoff →
    (∫ value,Complex.normSq (leadingGaussianValue (actualReferenceLaw C n (beta n)).weight
      (actualLeadingOutput C n (beta n) (MvPolynomial.monomial powers 1)) value) ∂FockGaussian.field) ≤
    (leadingGaussianFactor n cutoff * monomialWeight
      (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool ((n : ℝ)^2)) powers)^2 := by
  filter_upwards [actual_leading_seed_activity_eventually C hC beta hbeta,eventually_ge_atTop 1]
    with n he hn primaryPool bodyPool hp hb hpN hbN cutoff powers ho
  let seed := mixedMonomialSeed powers
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool ((n : ℝ)^2)
  have hw (s) : 0 ≤ weight s := inputWeight_nonneg _ _ _ _ _ s (sq_nonneg _)
  have hk : seed.primaryOrder+seed.bodyOrder ≤ cutoff := by rw [mixedMonomialSeed_order]; exact ho
  have hf : ((seed.primaryOrder+seed.bodyOrder).factorial : ℝ) ≤ cutoff.factorial := by exact_mod_cast Nat.factorial_le hk
  have hweight := mixedMonomialSeed_weight_le (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    primaryPool bodyPool ((n : ℝ)^2) (sq_nonneg _) powers
  have hscale : leadingActivityFactor n^(seed.primaryOrder+seed.bodyOrder)*weight seed ≤
      leadingActivityFactor n^cutoff*monomialWeight weight powers :=
    mul_le_mul (pow_le_pow_right₀ (leadingActivityFactor_ge_one n hn) hk) hweight (hw seed)
      (pow_nonneg (leadingActivityFactor_nonneg n) _)
  have hg := leadingSeedTensor_gaussian_energy (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (actualReferenceLaw C n (beta n)).weight (actualPrimaryChannel C n) (actualBodyChannel n) seed
  rw [mixedMonomialSeed_output] at hg
  apply hg.trans
  have ht := he primaryPool bodyPool hp hb hpN hbN seed
  apply (mul_le_mul hf ht (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)).trans
  have hs := pow_le_pow_left₀ (mul_nonneg (pow_nonneg (leadingActivityFactor_nonneg n) _) (hw seed)) hscale 2
  have hh := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg cutoff.factorial)
  simpa only [leadingGaussianFactor,mul_pow,Real.sq_sqrt (Nat.cast_nonneg cutoff.factorial),mul_assoc] using hh

end
end AFT.V7Calibration

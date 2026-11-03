import AFT.ActualBodyChannelProgram
import AFT.ActualReferenceProgram
import AFT.ActualPrimaryReciprocalProgram
import AFT.ActualDensityInverseBounds
import AFT.SingletonReferenceCoefficient
import AFT.IndependentBodyInverse
import AFT.OrderedSeedFactors

/-! # Actual rational reserved-body denominator coefficients -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics RepresentedPolynomial Filter
open scoped BigOperators

def actualBodyRawInputProgram (constant n : ℕ) (beta : ℚ) (output : ℕ) : ℚ :=
  (probabilityClamp (independentBodyPositiveProgram constant n beta output)-actualReferenceProgram constant n beta output)*
    actualPrimaryReciprocalProgram constant n beta output

def actualBodyInputProgram (constant n : ℕ) (beta : ℚ) (output : ℕ) : ℚ :=
  ∑ input∈Finset.range (ParameterProgram.modulus n).value,
    actualBodyRawInputProgram constant n beta input*actualDensityInverseProgram constant n beta input output

/-- The executable ordered finite reciprocal uses the same denominator
coefficient repeatedly and never compares two real seed labels. -/
def actualBodyReciprocalFactors (depth : ℕ) : OrderedSeedTable Unit :=
  (List.range (depth+1)).map (fun count => ⟨(-1 : ℚ)^count,List.replicate count ()⟩)

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
local instance bodyInputProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualBodyInputSeed (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :
    InputSeed (Fin (Parameters.modulus n)) :=
  inversePrimarySeed (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator
    (referenceCoefficientSeed (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta)
      (independentBodyPositiveMass C n beta) Finset.univ)

def actualBodyRawInput (C : ℝ) (n : ℕ) (beta : ℝ) (color : Fin (Parameters.modulus n)) : ℝ :=
  (independentBodyPositiveProfile C n beta color-(actualReferenceLaw C n beta).weight color)/
    (actualPrimaryLaw C n beta).weight color

theorem independentBodyInputTable_single_seed (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :
    independentBodyInputTable C n beta operator=MvPolynomial.X (actualBodyInputSeed C n beta operator) := by
  unfold independentBodyInputTable referenceInverseTable
  rw [referenceCoefficientTable_fin_one]
  simp only [inversePrimaryTable,MvPolynomial.aeval_X]
  rfl

theorem actualBodyInputSeed_scalar (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (output : Fin (Parameters.modulus n)) :
    (actualBodyInputSeed C n beta operator).kernel (fun _ => output)=
      ∑ input,actualBodyRawInput C n beta input*actualDensityInverseEntry C n beta operator input output := by
  unfold actualBodyInputSeed
  rw [inversePrimarySeed_singleton_constant _ _ _ _ _
    (by simp [referenceCoefficientSeed,primaryFiniteSeed]) rfl]
  apply Finset.sum_congr rfl
  intro input _
  have hh := referenceCoefficientSeed_fin_one_constant (actualPrimaryLaw C n beta)
    (actualReferenceLaw C n beta) (independentBodyPositiveProfile C n beta) input
  change (referenceCoefficientSeed (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta)
    (independentBodyPositiveMass C n beta) Finset.univ).kernel (fun _ => input)=_ at hh
  rw [hh,independentBodyPositiveProfile_mass,mul_one]
  rfl

/-- This is equality with the literal actual denominator, not merely with a
polynomial sharing its leading image. -/
theorem actualBodyReciprocalFactors_interpret (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) (depth : ℕ) :
    (actualBodyReciprocalFactors depth).interpret (fun _ => actualBodyInputSeed C n beta operator)=
      independentBodyReciprocal C n beta operator depth := by
  unfold actualBodyReciprocalFactors OrderedSeedTable.interpret independentBodyReciprocal finiteCorrection
  rw [independentBodyInputTable_single_seed]
  simp only [List.map_map,Function.comp_def,OrderedSeedTerm.interpret,List.map_replicate,List.prod_replicate,
    Rat.cast_pow,Rat.cast_neg,Rat.cast_one,MvPolynomial.smul_eq_C_mul,map_pow,map_neg,map_one]
  have hsum (f : ℕ → Table (InputSeed (Fin (Parameters.modulus n)))) (count : ℕ) :
      ((List.range count).map f).sum=∑ index∈Finset.range count,f index := by
    induction count with
    | zero => simp
    | succ count ih => rw [List.sum_range_succ,Finset.sum_range_succ,ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro count _
  rw [neg_pow]
  ring

def actualBodyRawInputProgramError (n : ℕ) : ℝ :=
  16*(n : ℝ)^40*independentBodyPositiveProgramError n+actualPrimaryReciprocalProgramError n

def actualBodyInputProgramError (n : ℕ) : ℝ :=
  514*(n : ℝ)^160*actualBodyRawInputProgramError n+
    32*(n : ℝ)^80*actualDensityInverseProgramError n

theorem actualBodyRawInputProgramError_negligible : Negligible actualBodyRawInputProgramError := by
  convert ((independentBodyPositiveProgramError_negligible.mul_polynomial 40).const_mul 16).add
    actualPrimaryReciprocalProgramError_negligible using 1
  funext n;unfold actualBodyRawInputProgramError;ring

theorem actualBodyInputProgramError_negligible : Negligible actualBodyInputProgramError := by
  convert ((actualBodyRawInputProgramError_negligible.mul_polynomial 160).const_mul 514).add
    ((actualDensityInverseProgramError_negligible.mul_polynomial 80).const_mul 32) using 1
  funext n;unfold actualBodyInputProgramError;ring

private theorem probability_difference_abs_le (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : |a-b| ≤ 1 := abs_le.mpr (by constructor <;> linarith)

theorem actual_body_raw_input_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ color : Fin (Parameters.modulus n),
      |actualBodyRawInput constant n (beta n) color| ≤ 16*(n : ℝ)^40 ∧
      |(actualBodyRawInputProgram constant n (beta n) color.val : ℝ)| ≤ 16*(n : ℝ)^40 ∧
      |(actualBodyRawInputProgram constant n (beta n) color.val : ℝ)-actualBodyRawInput constant n (beta n) color| ≤
        actualBodyRawInputProgramError n := by
  filter_upwards [independent_body_positive_program_eventually constant hc beta hbeta,
    actual_reference_program_eventually constant hc beta hbeta,
    actual_primary_reciprocal_program_eventually constant hc beta hbeta,
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    eventually_ge_atTop 2] with n hbody href hrec hlow hn color
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hq0 : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hp0 : 0 < (actualPrimaryLaw constant n (beta n)).weight color := lt_of_lt_of_le (by positivity) (hlow color)
  have hinverse : |((actualPrimaryLaw constant n (beta n)).weight color)⁻¹| ≤ 16*(n : ℝ)^40 := by
    rw [abs_of_pos (inv_pos.mpr hp0)]
    have hh := one_div_le_one_div_of_le (by positivity : 0 < 1/(4*(Parameters.modulus n : ℝ))) (hlow color)
    simp only [one_div,inv_inv] at hh
    exact hh.trans (by linarith)
  have hbody0 := independentBodyPositiveProfile_nonneg (constant : ℝ) n (beta n) color
  have hbody1 : independentBodyPositiveProfile constant n (beta n) color ≤ 1 := by
    simpa only [independentBodyPositiveProfile_mass] using Finset.single_le_sum
      (fun input (_ : input∈Finset.univ) => independentBodyPositiveProfile_nonneg (constant : ℝ) n (beta n) input)
      (Finset.mem_univ color)
  have hr0 := (actualReferenceLaw (constant : ℝ) n (beta n)).nonneg color
  have hr1 : (actualReferenceLaw constant n (beta n)).weight color ≤ 1 := by
    simpa only [(actualReferenceLaw (constant : ℝ) n (beta n)).sum_one] using Finset.single_le_sum
      (fun input (_ : input∈Finset.univ) => (actualReferenceLaw (constant : ℝ) n (beta n)).nonneg input)
      (Finset.mem_univ color)
  have htrue := probability_difference_abs_le _ _ hbody0 hbody1 hr0 hr1
  have hb := probabilityClamp_bounds (independentBodyPositiveProgram constant n (beta n) color.val)
  have happrox := probability_difference_abs_le _ _ hb.1 hb.2 hr0 hr1
  have hbe := (probabilityClamp_error _ _ hbody0 hbody1).trans (hbody color)
  have hbe0 := (abs_nonneg _).trans hbe
  have hre0 := (abs_nonneg _).trans (hrec color).2.2
  simp only [actualBodyRawInputProgram,Rat.cast_mul,Rat.cast_sub,href color,actualBodyRawInput,div_eq_mul_inv]
  refine ⟨?_,?_,?_⟩
  · rw [abs_mul]
    exact (mul_le_mul htrue hinverse (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · rw [abs_mul,abs_of_pos (hrec color).1]
    exact (mul_le_mul happrox (hrec color).2.1 (hrec color).1.le (by norm_num)).trans_eq (one_mul _)
  · apply (approximation_mul_error _ _ _ _).trans
    have hdiff : |((probabilityClamp (independentBodyPositiveProgram constant n (beta n) color.val) : ℝ)-
        (actualReferenceLaw constant n (beta n)).weight color)-
        (independentBodyPositiveProfile constant n (beta n) color-(actualReferenceLaw constant n (beta n)).weight color)| ≤
        independentBodyPositiveProgramError n := by simpa only [sub_sub_sub_cancel_right] using hbe
    exact (add_le_add (mul_le_mul hdiff hinverse (abs_nonneg _) hbe0)
      (mul_le_mul happrox (hrec color).2.2 (abs_nonneg _) (by norm_num))).trans_eq (by
        unfold actualBodyRawInputProgramError;ring)

theorem actual_body_input_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse (constant : ℝ) n →∀ output : Fin (Parameters.modulus n),
      |(actualBodyInputProgram constant n (beta n) output.val : ℝ)-
        (actualBodyInputSeed constant n (beta n) operator).kernel (fun _ => output)| ≤ actualBodyInputProgramError n := by
  filter_upwards [actual_body_raw_input_program_eventually constant hc beta hbeta,
    actual_density_inverse_estimates_eventually constant hc beta hbeta,eventually_ge_atTop 2]
    with n hraw hmatrix hn operator hop output
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hR0 : 0 ≤ actualBodyRawInputProgramError n := (abs_nonneg _).trans (hraw output).2.2
  have hM0 : 0 ≤ actualDensityInverseProgramError n := (abs_nonneg _).trans (hmatrix operator hop output output).2.2
  have hcast : (actualBodyInputProgram constant n (beta n) output.val : ℝ)=
      ∑ input : Fin (Parameters.modulus n),(actualBodyRawInputProgram constant n (beta n) input.val : ℝ)*
        (actualDensityInverseProgram constant n (beta n) input.val output.val : ℝ) := by
    simp only [actualBodyInputProgram,Rat.cast_sum,Rat.cast_mul,ParameterProgram.modulus_value]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [hcast,actualBodyInputSeed_scalar,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _input : Fin (Parameters.modulus n),
        (actualBodyRawInputProgramError n*(257*(n : ℝ)^120)+16*(n : ℝ)^40*actualDensityInverseProgramError n) := by
      apply Finset.sum_le_sum
      intro input _
      apply (approximation_mul_error _ _ _ _).trans
      exact add_le_add
        (mul_le_mul (hraw input).2.2 (hmatrix operator hop input output).1 (abs_nonneg _) hR0)
        (mul_le_mul (hraw input).2.1 (hmatrix operator hop input output).2.2 (abs_nonneg _) (by positivity))
    _ = (Parameters.modulus n : ℝ)*(actualBodyRawInputProgramError n*(257*(n : ℝ)^120)+
        16*(n : ℝ)^40*actualDensityInverseProgramError n) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ ≤ (2*(n : ℝ)^40)*(actualBodyRawInputProgramError n*(257*(n : ℝ)^120)+
        16*(n : ℝ)^40*actualDensityInverseProgramError n) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by unfold actualBodyInputProgramError;ring

end
end AFT.V7Calibration

import AFT.ActualPreconditionedBounds
import AFT.PreconditionedIteration

/-! # A finite rational iteration for the actual V7 primary inverse -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- This is the physical body-minus-root anchor matrix, with no source
resampling or substitution of the compensating root by a leg error. -/
def actualAnchorErrorProgram (constant n input output : ℕ) : ℚ :=
  actualAnchorProgram constant n false input output-actualAnchorProgram constant n true input output

def actualPreconditionedMatrixProgram (constant n input output : ℕ) : ℚ :=
  ∑ middle∈Finset.range (ParameterProgram.modulus n).value,
    actualRankInverseProgram constant n middle output*actualAnchorErrorProgram constant n input middle

def actualInverseIterationProgram (constant n input : ℕ) : ℕ → ℕ → ℚ
  | 0 => fun _ => 0
  | steps+1 => fun output => actualRankInverseProgram constant n input output-
      ∑ middle∈Finset.range (ParameterProgram.modulus n).value,
        actualPreconditionedMatrixProgram constant n middle output*
          actualInverseIterationProgram constant n input steps middle

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance inverseIterationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualRankApprox (constant n : ℕ) : Module.End ℝ (Fin (Parameters.modulus n) → ℝ) :=
  realMatrixOperator (fun output input => actualRankInverseProgram constant n input.val output.val)

def actualErrorApprox (constant n : ℕ) : Module.End ℝ (Fin (Parameters.modulus n) → ℝ) :=
  realMatrixOperator (fun output input => actualAnchorErrorProgram constant n input.val output.val)

def actualRankActivityError (n : ℕ) : ℝ := 16*(n : ℝ)^40*actualRankInverseProgramError n

def actualAnchorActivityError (n : ℕ) : ℝ := 32*(n : ℝ)^40*actualPairSourceProgramError n

theorem actualRankActivityError_nonneg (n : ℕ) : 0≤actualRankActivityError n := by
  unfold actualRankActivityError actualRankInverseProgramError actualRankDenominatorProgramError
    actualNormalizedSignProgramError actualActivationInverseError actualPairSourceProgramError
    actualBodyBlurProgramError actualRootMarginalError
  positivity

theorem actualAnchorActivityError_nonneg (n : ℕ) : 0≤actualAnchorActivityError n := by
  unfold actualAnchorActivityError actualPairSourceProgramError actualBodyBlurProgramError actualRootMarginalError
  positivity

theorem actualRankActivityError_negligible : Negligible actualRankActivityError := by
  convert (actualRankInverseProgramError_negligible.mul_polynomial 40).const_mul 16 using 1
  funext n
  unfold actualRankActivityError
  ring

theorem actualAnchorActivityError_negligible : Negligible actualAnchorActivityError := by
  convert (actualPairSourceProgramError_negligible.mul_polynomial 40).const_mul 32 using 1
  funext n
  unfold actualAnchorActivityError
  ring

theorem linearMap_basis_matrix {Color : Type*} [Fintype Color] [DecidableEq Color]
    (operator : Module.End ℝ (Color → ℝ)) (profile : Color → ℝ) :
    (fun output => ∑ input,operator (Pi.single input 1) output*profile input)=operator profile := by
  classical
  have hrepr : (∑ input,profile input • (Pi.single input 1 : Color → ℝ))=profile := by
    funext output
    simp [Pi.single_apply]
  have hh := congrArg operator hrepr
  simp only [map_sum,map_smul] at hh
  convert hh using 1
  funext output
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro input _
  ring

theorem actual_rank_approx_error_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ profile,
      primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n)
        (actualRankApprox constant n profile-actualNormalizedRankInverse (constant : ℝ) n profile)≤
        actualRankActivityError n*primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) profile := by
  filter_upwards [actual_rank_inverse_program_eventually constant hc,
    analysisPrimary_estimates_eventually (constant : ℝ) (by exact_mod_cast hc),analysisRate_bounds_eventually,
    eventually_ge_atTop 2] with n he hp hr hn profile
  have hq : 0<(Parameters.modulus n : ℝ) := by exact_mod_cast (Parameters.modulus_prime n).pos
  have he0 : 0≤actualRankInverseProgramError n := by
    unfold actualRankInverseProgramError actualRankDenominatorProgramError actualNormalizedSignProgramError
      actualActivationInverseError actualPairSourceProgramError actualBodyBlurProgramError actualRootMarginalError
    positivity
  have hh := rationalMatrix_difference_primaryActivity
    (fun output input : Fin (Parameters.modulus n) => actualRankInverseProgram constant n input.val output.val)
    (fun output input => actualNormalizedRankInverse (constant : ℝ) n (Pi.single input 1) output)
    profile (analysisPrimary (constant : ℝ) n) (analysisRate n) (1/(4*(Parameters.modulus n : ℝ)))
    (actualRankInverseProgramError n) hr.1.le (by positivity) hp.1 hp.2.1 he0 (fun output input => he input output)
  rw [linearMap_basis_matrix] at hh
  have hqbound : (Parameters.modulus n : ℝ)≤2*(n : ℝ)^40 := by
    have h := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at h
    exact_mod_cast h
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (primaryActivity_nonneg _ _ _ hr.1.le)
  unfold actualRankActivityError
  simp only [div_eq_mul_inv,one_mul,inv_inv]
  have hprod := mul_le_mul_of_nonneg_left (show 1+analysisRate n≤2 by linarith) (by positivity : 0≤actualRankInverseProgramError n*(4*(Parameters.modulus n : ℝ)))
  nlinarith [mul_le_mul_of_nonneg_left hqbound he0]

theorem actual_anchor_error_program_eventually (constant : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (input output : Fin (Parameters.modulus n)),
      |(actualAnchorErrorProgram constant n input.val output.val : ℝ)-
        (actualAnchorMatrix (constant : ℝ) n false input output.val-
          actualAnchorMatrix (constant : ℝ) n true input output.val)|≤2*actualPairSourceProgramError n := by
  filter_upwards [actual_anchor_program_eventually constant] with n hh input output
  simp only [actualAnchorErrorProgram,Rat.cast_sub]
  exact (approximation_sub_error _ _ _ _).trans ((add_le_add (hh false input output.val) (hh true input output.val)).trans_eq (by ring))

theorem actualAnchorError_matrix (constant : ℝ) (n : ℕ) (profile : Fin (Parameters.modulus n) → ℝ) :
    (fun output => ∑ input,(actualAnchorMatrix constant n false input output.val-
      actualAnchorMatrix constant n true input output.val)*profile input)=actualAnchorError constant n profile := by
  funext output
  rw [actualAnchorError,anchorError_apply_formula]
  apply Finset.sum_congr rfl
  intro input _
  simp only [actualAnchorMatrix,Bool.false_eq_true,if_false,if_true]
  ring

theorem actual_anchor_approx_error_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ profile,
      primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n)
        (actualErrorApprox constant n profile-actualAnchorError (constant : ℝ) n profile)≤
        actualAnchorActivityError n*primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) profile := by
  filter_upwards [actual_anchor_error_program_eventually constant,
    analysisPrimary_estimates_eventually (constant : ℝ) (by exact_mod_cast hc),analysisRate_bounds_eventually,
    eventually_ge_atTop 2] with n he hp hr hn profile
  have hq : 0<(Parameters.modulus n : ℝ) := by exact_mod_cast (Parameters.modulus_prime n).pos
  have he0 : 0≤actualPairSourceProgramError n := by
    unfold actualPairSourceProgramError actualBodyBlurProgramError actualRootMarginalError
    positivity
  have hh := rationalMatrix_difference_primaryActivity
    (fun output input : Fin (Parameters.modulus n) => actualAnchorErrorProgram constant n input.val output.val)
    (fun output input => actualAnchorMatrix (constant : ℝ) n false input output.val-
      actualAnchorMatrix (constant : ℝ) n true input output.val)
    profile (analysisPrimary (constant : ℝ) n) (analysisRate n) (1/(4*(Parameters.modulus n : ℝ)))
    (2*actualPairSourceProgramError n) hr.1.le (by positivity) hp.1 hp.2.1 (by positivity) (fun output input => he input output)
  rw [actualAnchorError_matrix] at hh
  have hqbound : (Parameters.modulus n : ℝ)≤2*(n : ℝ)^40 := by
    have h := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at h
    exact_mod_cast h
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (primaryActivity_nonneg _ _ _ hr.1.le)
  unfold actualAnchorActivityError
  simp only [div_eq_mul_inv,one_mul,inv_inv]
  have hprod := mul_le_mul_of_nonneg_left (show 1+analysisRate n≤2 by linarith) (by positivity : 0≤2*actualPairSourceProgramError n*(4*(Parameters.modulus n : ℝ)))
  nlinarith [mul_le_mul_of_nonneg_left hqbound he0]

end
end AFT.V7Calibration

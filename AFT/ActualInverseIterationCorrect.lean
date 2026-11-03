import AFT.ActualInverseIterationProgram

/-! # The rational iteration approximates the genuine physical inverse -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance inverseIterationCorrectFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem actualRankApprox_basis (constant n : ℕ) (input output : Fin (Parameters.modulus n)) :
    actualRankApprox constant n (Pi.single input 1) output=(actualRankInverseProgram constant n input.val output.val : ℝ) := by
  simp [actualRankApprox,realMatrixOperator,Pi.single_apply]

theorem actualPreconditionedMatrixProgram_cast (constant n : ℕ)
    (input output : Fin (Parameters.modulus n)) :
    (actualPreconditionedMatrixProgram constant n input.val output.val : ℝ)=
      ∑ middle : Fin (Parameters.modulus n),
        (actualRankInverseProgram constant n middle.val output.val : ℝ)*
          actualAnchorErrorProgram constant n input.val middle.val := by
  simp only [actualPreconditionedMatrixProgram,Rat.cast_sum,Rat.cast_mul,ParameterProgram.modulus_value]
  exact (Fin.sum_univ_eq_sum_range (fun middle =>
    (actualRankInverseProgram constant n middle output.val : ℝ)*actualAnchorErrorProgram constant n input.val middle) _).symm

theorem actualPreconditionedMatrixProgram_apply (constant n : ℕ)
    (profile : Fin (Parameters.modulus n) → ℝ) (output : Fin (Parameters.modulus n)) :
    (∑ input : Fin (Parameters.modulus n),
      (actualPreconditionedMatrixProgram constant n input.val output.val : ℝ)*profile input)=
      actualRankApprox constant n (actualErrorApprox constant n profile) output := by
  simp only [actualPreconditionedMatrixProgram_cast,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [actualRankApprox,actualErrorApprox,realMatrixOperator,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.mul_sum,mul_assoc]

theorem actualInverseIterationProgram_cast (constant n : ℕ)
    (input : Fin (Parameters.modulus n)) (steps : ℕ) :
    (fun output : Fin (Parameters.modulus n) => (actualInverseIterationProgram constant n input.val steps output.val : ℝ))=
      realLinearIteration ((actualRankApprox constant n).comp (actualErrorApprox constant n))
        (actualRankApprox constant n (Pi.single input 1)) steps := by
  induction steps with
  | zero => ext output;simp [actualInverseIterationProgram,realLinearIteration]
  | succ steps ih =>
    funext output
    simp only [actualInverseIterationProgram,realLinearIteration,Pi.sub_apply,Rat.cast_sub,Rat.cast_sum,
      Rat.cast_mul,ParameterProgram.modulus_value,LinearMap.comp_apply,actualRankApprox_basis]
    congr 1
    rw [←Fin.sum_univ_eq_sum_range (fun middle =>
      (actualPreconditionedMatrixProgram constant n middle output.val : ℝ)*
        (actualInverseIterationProgram constant n input.val steps middle : ℝ))]
    rw [actualPreconditionedMatrixProgram_apply,ih]

def actualInverseIterationError (n steps : ℕ) : ℝ :=
  2*(1/2 : ℝ)^steps+10*actualRankActivityError n+16*actualAnchorActivityError n

theorem actual_inverse_iteration_correct_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
        operator.toLinearMap=actualResponse (constant : ℝ) n ∧
        ∀ (input : Fin (Parameters.modulus n)) (steps : ℕ),
          primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n)
            ((fun output : Fin (Parameters.modulus n) => (actualInverseIterationProgram constant n input.val steps output.val : ℝ))-
              operator.symm (Pi.single input 1))≤
            actualInverseIterationError n steps*primaryActivity (analysisRate n)
              (analysisPrimary (constant : ℝ) n) (Pi.single input 1) := by
  have hinverse := actual_response_inverse_eventually (κ := Unit) (constant : ℝ) (by exact_mod_cast hc)
    analysisBeta Parameters.legs (by filter_upwards [] with n; exact ⟨(analysisBeta_typical n).1,(analysisBeta_typical n).2,by omega⟩)
  have hsmallR := actualRankActivityError_negligible.tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ)<1/100)
  have hsmallE := actualAnchorActivityError_negligible.tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ)<1/100)
  filter_upwards [hinverse,actual_rank_preconditioner_exact_eventually (constant : ℝ) (by exact_mod_cast hc),
    actual_rank_activity_bound_eventually (constant : ℝ) (by exact_mod_cast hc),
    actual_anchor_activity_bound_eventually (constant : ℝ) (by exact_mod_cast hc),
    actual_preconditioned_contraction_eventually (constant : ℝ) (by exact_mod_cast hc),
    actual_rank_approx_error_eventually constant hc,actual_anchor_approx_error_eventually constant hc,
    analysisPrimary_estimates_eventually (constant : ℝ) (by exact_mod_cast hc),analysisRate_bounds_eventually,
    hsmallR,hsmallE] with n hi hex hr he ht hrd hed hp hrate hsR hsE
  obtain ⟨operator,hop,hbound,_⟩ := hi
  refine ⟨operator,hop,?_⟩
  have hq : 0<(Parameters.modulus n : ℝ) := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hp' : ∀color,0<analysisPrimary (constant : ℝ) n color := fun color => lt_of_lt_of_le (by positivity) (hp.1 color)
  let combined := actualRankActivityError n*(1/16+actualAnchorActivityError n)+4*actualAnchorActivityError n
  have hR0 := actualRankActivityError_nonneg n
  have hE0 := actualAnchorActivityError_nonneg n
  have hcombined0 : 0≤combined := by dsimp [combined];positivity
  have hcombined : combined≤2*actualRankActivityError n+4*actualAnchorActivityError n := by
    dsimp [combined]
    have hh := mul_le_mul_of_nonneg_left (show 1/16+actualAnchorActivityError n≤2 by linarith) hR0
    linarith
  have hcombinedSmall : combined≤1/4 := by linarith
  have hdiff := primaryActivity_composition_perturbation (analysisPrimary (constant : ℝ) n) (analysisRate n)
    4 (1/16) (actualRankActivityError n) (actualAnchorActivityError n)
    (actualNormalizedRankInverse (constant : ℝ) n) (actualAnchorError (constant : ℝ) n)
    (actualRankApprox constant n) (actualErrorApprox constant n) hrate.1.le hp' hR0 hr he hrd hed
  have hcontract : ∀ profile,primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n)
      (actualRankApprox constant n (actualErrorApprox constant n profile))≤
      (1/2)*primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) profile := by
    intro profile
    have hh := primaryActivity_operator_perturbation (analysisPrimary (constant : ℝ) n) (analysisRate n)
      (1/4) combined ((actualNormalizedRankInverse (constant : ℝ) n).comp (actualAnchorError (constant : ℝ) n))
      ((actualRankApprox constant n).comp (actualErrorApprox constant n)) hrate.1.le hp' ht hdiff profile
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : 1/4+combined≤1/2) (primaryActivity_nonneg _ _ _ hrate.1.le))
  intro input steps
  let target : Fin (Parameters.modulus n) → ℝ := Pi.single input 1
  let solution := operator.symm target
  have hsolution : actualNormalizedRankInverse (constant : ℝ) n target-
      actualNormalizedRankInverse (constant : ℝ) n (actualAnchorError (constant : ℝ) n solution)=solution := by
    have hresponse : actualResponse (constant : ℝ) n solution=target := by
      rw [←hop]
      exact operator.apply_symm_apply target
    have hh := congrArg (actualNormalizedRankInverse (constant : ℝ) n) hresponse
    change actualNormalizedRankInverse (constant : ℝ) n
      (primaryRankOperator (v7Activation (constant : ℝ) n)
        (signResponse n (constant : ℝ) (boundaryHalf (constant : ℝ) n)
          (startsPlus (constant : ℝ) n) (startsMinus (constant : ℝ) n)
          (pairSourceShift (constant : ℝ) n) (pairSourceLaw (constant : ℝ) n))
        (profileSignMap (paletteSign (Parameters.modulus n))) solution+actualAnchorError (constant : ℝ) n solution)=_ at hh
    rw [map_add,(hex solution).1] at hh
    exact (eq_sub_iff_add_eq.mpr hh).symm
  have hres := preconditioned_residual_bound (analysisPrimary (constant : ℝ) n) (analysisRate n)
    4 (1/16) (actualRankActivityError n) (actualAnchorActivityError n) 2
    (actualNormalizedRankInverse (constant : ℝ) n) (actualAnchorError (constant : ℝ) n)
    (actualRankApprox constant n) (actualErrorApprox constant n) target solution
    hrate.1.le hp' hR0 hcombined0 hr he hrd hed hsolution (hbound target)
  have htarget0 := primaryActivity_nonneg (analysisRate n) (analysisPrimary (constant : ℝ) n) target hrate.1.le
  have herror0 : 0≤(actualRankActivityError n+2*combined)*primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) target := by positivity
  have hiter := primaryActivity_iteration_error ((actualRankApprox constant n).comp (actualErrorApprox constant n))
    (actualRankApprox constant n target) solution (analysisRate n) (analysisPrimary (constant : ℝ) n)
    ((actualRankActivityError n+2*combined)*primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) target)
    hrate.1.le hp' herror0 hcontract hres steps
  rw [actualInverseIterationProgram_cast]
  apply hiter.trans
  have hb := mul_le_mul_of_nonneg_left (hbound target) (by positivity : 0≤(1/2 : ℝ)^steps)
  change (1/2 : ℝ)^steps*primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) solution≤
    (1/2 : ℝ)^steps*(2*primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) target) at hb
  have hcb := mul_le_mul_of_nonneg_right hcombined htarget0
  unfold actualInverseIterationError
  change _≤_*primaryActivity (analysisRate n) (analysisPrimary (constant : ℝ) n) target
  nlinarith only [hb,hcb]

end
end AFT.V7Calibration

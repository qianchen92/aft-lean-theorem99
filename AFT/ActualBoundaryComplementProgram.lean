import AFT.ActualBoundaryDensityProgram
import AFT.ActualUnactivatedInverseProgram
import AFT.ActualBoundaryComplement

/-! # Executable actual legal-complement entries -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- The finite intermediate-color sum is the true inverse composed with
boundary collapse. No forward matrix or real-valued seed label is used. -/
def actualBoundaryComplementProgram (constant n : ℕ) (beta : ℚ) (input output : ℕ) : ℚ :=
  ∑ middle∈Finset.range (ParameterProgram.modulus n).value,
    actualUnactivatedInverseProgram constant n beta middle output*
      actualBoundaryDensityProgram constant n beta input middle

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
local instance boundaryComplementProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualBoundaryComplementProgramError (n : ℕ) : ℝ :=
  34*(n : ℝ)^80*actualUnactivatedInverseProgramError n+
    514*(n : ℝ)^160*actualBoundaryDensityProgramError n

theorem actualBoundaryComplementProgramError_negligible : Negligible actualBoundaryComplementProgramError := by
  convert ((actualUnactivatedInverseProgramError_negligible.mul_polynomial 80).const_mul 34).add
    ((actualBoundaryDensityProgramError_negligible.mul_polynomial 160).const_mul 514) using 1
  funext n;unfold actualBoundaryComplementProgramError;ring

def actualBoundaryComplementEntry (constant : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (input output : Fin (Parameters.modulus n)) : ℝ :=
  densityMatrixEntry (actualPrimaryLaw constant n beta).weight
    (LinearMap.id-legalInputProjection operator (boundaryIdealProjection
      (boundaryPalette (Parameters.modulus n) (boundaryHalf constant n))ᶜ
      (actualPrimaryLaw constant n beta).weight)) input output

theorem actual_boundary_complement_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse (constant : ℝ) n →∀ input output,
      |actualBoundaryComplementEntry constant n (beta n) operator input output| ≤ 10000*(n : ℝ)^200 ∧
      |(actualBoundaryComplementProgram constant n (beta n) input.val output.val : ℝ)| ≤ 10000*(n : ℝ)^200 ∧
      |(actualBoundaryComplementProgram constant n (beta n) input.val output.val : ℝ)-
        actualBoundaryComplementEntry constant n (beta n) operator input output| ≤ actualBoundaryComplementProgramError n := by
  filter_upwards [actual_boundary_density_program_eventually constant hc beta hbeta,
    actual_unactivated_inverse_program_eventually constant hc beta hbeta,
    actual_response_difference_interior_eventually (constant : ℝ) (by exact_mod_cast hc),
    actual_primary_law_quarter_lower_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    eventually_ge_atTop 2] with n hb hi hr hp hn operator hop input output
  have hq0 : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hpos (color) : (actualPrimaryLaw constant n (beta n)).weight color≠0 :=
    ne_of_gt ((by positivity : (0 : ℝ)<1/(4*(Parameters.modulus n : ℝ))).trans_le (hp color))
  have hrange : ∀ profile,operator profile-profile∈canonicalInteriorProfiles
      (boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n))ᶜ := by
    intro profile
    simpa only [canonicalInteriorProfiles,Finset.mem_compl] using (hr operator hop profile).1
  let first := densityMatrixEntry (actualPrimaryLaw constant n (beta n)).weight operator.symm.toLinearMap
  let second := boundaryDensityEntry (boundaryPalette (Parameters.modulus n) (boundaryHalf (constant : ℝ) n))ᶜ
    (actualPrimaryLaw constant n (beta n)).weight
  let firstApprox := fun input output : Fin (Parameters.modulus n) =>
    (actualUnactivatedInverseProgram constant n (beta n) input.val output.val : ℝ)
  let secondApprox := fun input output : Fin (Parameters.modulus n) =>
    (actualBoundaryDensityProgram constant n (beta n) input.val output.val : ℝ)
  have hexact : actualBoundaryComplementEntry constant n (beta n) operator input output=
      ∑ middle,first middle output*second input middle := by
    unfold actualBoundaryComplementEntry
    rw [legalInputProjection_complement _ _ operator hrange,densityMatrixEntry_comp _ hpos]
    simp only [first,second,boundaryDensityEntry_eq _ _ hpos]
  have hprog : (actualBoundaryComplementProgram constant n (beta n) input.val output.val : ℝ)=
      ∑ middle,firstApprox middle output*secondApprox input middle := by
    simp only [actualBoundaryComplementProgram,ParameterProgram.modulus_value,Rat.cast_sum,Rat.cast_mul]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  have hu0 : 0 ≤ actualUnactivatedInverseProgramError n := (abs_nonneg _).trans (hi operator hop input output).2.2
  have hb0 : 0 ≤ actualBoundaryDensityProgramError n := (abs_nonneg _).trans (hb input output).2.2
  have hbound : (Parameters.modulus n : ℝ)*(257*(n : ℝ)^120)*(17*(n : ℝ)^40) ≤ 10000*(n : ℝ)^200 := by
    calc
      _ ≤ (2*(n : ℝ)^40)*(257*(n : ℝ)^120)*(17*(n : ℝ)^40) := by gcongr
      _ = 8738*(n : ℝ)^200 := by ring
      _ ≤ _ := by gcongr; norm_num
  rw [hexact,hprog]
  refine ⟨?_,?_,?_⟩
  · exact (matrixComposition_abs_le first second (257*(n : ℝ)^120) (17*(n : ℝ)^40)
      (by positivity) (fun i o => (hi operator hop i o).1) (fun i o => (hb i o).1) input output).trans
        (by simpa only [Fintype.card_fin] using hbound)
  · exact (matrixComposition_abs_le firstApprox secondApprox (257*(n : ℝ)^120) (17*(n : ℝ)^40)
      (by positivity) (fun i o => (hi operator hop i o).2.1) (fun i o => (hb i o).2.1) input output).trans
        (by simpa only [Fintype.card_fin] using hbound)
  · have hh := matrixComposition_error first firstApprox second secondApprox (257*(n : ℝ)^120) (17*(n : ℝ)^40)
      (actualUnactivatedInverseProgramError n) (actualBoundaryDensityProgramError n)
      (by positivity) (by positivity) hu0 hb0 (fun i o => (hi operator hop i o).2.1)
      (fun i o => (hb i o).1) (fun i o => (hi operator hop i o).2.2) (fun i o => (hb i o).2.2) input output
    simp only [Fintype.card_fin] at hh
    apply hh.trans
    calc
      _ ≤ (2*(n : ℝ)^40)*(actualUnactivatedInverseProgramError n*(17*(n : ℝ)^40)+
          (257*(n : ℝ)^120)*actualBoundaryDensityProgramError n) := by gcongr
      _ = actualBoundaryComplementProgramError n := by unfold actualBoundaryComplementProgramError;ring

end
end AFT.V7Calibration

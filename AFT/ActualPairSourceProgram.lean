import AFT.ActualBodyBlurProgram

/-! # The actual shared pair-source law has an executable rational table -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

abbrev ActualPairProgramSample (constant n : ℕ) :=
  ActualBodyProgramSample constant n × Window (actualLegCutoffProgram constant n-1)

def actualPairSourceProgram (constant n : ℕ) (point : ActualPairProgramSample constant n) : ℚ :=
  actualBodyBlurProgram constant n point.1*
    windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n point.2

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance pairSourceProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualPairProgramEquiv (constant n : ℕ) : ActualPairProgramSample constant n≃pairSample (constant : ℝ) n :=
  (actualBodyProgramEquiv constant n).prodCongr (actualLegWindowEquiv constant n)

theorem actualPairProgramEquiv_apply (constant n : ℕ) (point : ActualPairProgramSample constant n) :
    actualPairProgramEquiv constant n point=(actualBodyProgramEquiv constant n point.1,actualLegWindowEquiv constant n point.2) := rfl

def actualPairSourceApproxLaw (constant n : ℕ)
    (hroot : 0<RootSlice.sumProbability (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n) 0) :
    FiniteDist (pairSample (constant : ℝ) n) :=
  (actualBodyBlurApproxLaw constant n hroot).prod (actualLegTicketLaw constant 10 n n)

theorem actualPairSourceProgram_cast (constant n : ℕ)
    (hroot : 0<RootSlice.sumProbability (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n) 0)
    (point : ActualPairProgramSample constant n) :
    (actualPairSourceProgram constant n point : ℝ)=
      (actualPairSourceApproxLaw constant n hroot).weight (actualPairProgramEquiv constant n point) := by
  simp only [actualPairSourceProgram,Rat.cast_mul,actualBodyBlurProgram_cast constant n hroot,
    actualPairSourceApproxLaw,FiniteDist.prod_weight,actualPairProgramEquiv_apply,actualLegTicketLaw_program_weight]

def actualPairSourceProgramError (n : ℕ) : ℝ := actualBodyBlurProgramError n+1/(2 : ℝ)^n

theorem actualPairSourceProgramError_negligible : Negligible actualPairSourceProgramError := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n
    simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  exact actualBodyBlurProgramError_negligible.add hm

/-- This is the actual source shared between the endpoint-pair chart and
the attached body. Its complete law is approximated, preserving that shared
sample rather than replacing it by independent copies. -/
theorem actual_pair_source_program_eventually (constant : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ point : ActualPairProgramSample constant n,
        |(actualPairSourceProgram constant n point : ℝ)-
          (pairSourceLaw (constant : ℝ) n).weight (actualPairProgramEquiv constant n point)|)≤
        actualPairSourceProgramError n := by
  filter_upwards [actual_root_ticket_acceptance_eventually,actual_body_blur_program_eventually constant,
    eventually_ge_atTop 2] with n hroot hbody hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hp : 0<RootSlice.sumProbability (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n) 0 :=
    (by positivity : (0 : ℝ)<1/(n : ℝ)^32).trans_le hroot
  have hb : (∑ point,|(actualBodyBlurApproxLaw constant n hp).weight point-(bodyBlur (constant : ℝ) n).weight point|)≤
      actualBodyBlurProgramError n := by
    convert hbody using 1
    symm
    simp only [actualBodyBlurProgram_cast constant n hp]
    convert (actualBodyProgramEquiv constant n).sum_comp (fun point =>
      |(actualBodyBlurApproxLaw constant n hp).weight point-(bodyBlur (constant : ℝ) n).weight point|) using 1
  have hl : (∑ point,|(actualLegTicketLaw constant 10 n n).weight point-
      (windowGaussian (10*n) (legCutoff (constant : ℝ) n-1)).weight point|)≤1/(2 : ℝ)^n := by
    simpa only [Nat.cast_ofNat] using actualLegTicketLaw_l1 constant 10 n n (by decide) (by omega)
  have hh := (FiniteDist.l1_prod_le _ _ _ _).trans (add_le_add hb hl)
  have heq : (∑ point : ActualPairProgramSample constant n,|(actualPairSourceProgram constant n point : ℝ)-
      (pairSourceLaw (constant : ℝ) n).weight (actualPairProgramEquiv constant n point)|)=
      ∑ point,|(actualPairSourceApproxLaw constant n hp).weight point-(pairSourceLaw (constant : ℝ) n).weight point| := by
    simp only [actualPairSourceProgram_cast constant n hp]
    convert (actualPairProgramEquiv constant n).sum_comp (fun point =>
      |(actualPairSourceApproxLaw constant n hp).weight point-(pairSourceLaw (constant : ℝ) n).weight point|) using 1
  rw [heq]
  exact hh

end
end AFT.V7Calibration

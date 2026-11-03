import AFT.ActualAuxiliaryGaussianProgram
import AFT.ActualRootMarginalProgram

/-! # A rational program for the actual root/leg/queue body-blur table -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram Filter
open scoped BigOperators

abbrev ActualBodyProgramSample (constant n : ℕ) :=
  Window (3*n^2-1) × Option (Window (actualLegCutoffProgram constant n-1)) × Option (Window (n^2-1))

def actualLegRateProgram (n : ℕ) : ℚ := ((max 2 n : ℕ) : ℚ)^30/actualRootPopulationProgram n

def actualQueueRateProgram (n : ℕ) : ℚ := (ParameterProgram.modulus n).value/(actualRootPopulationProgram n : ℚ)

def optionalWeightProgram {Source : Type*} (rate : ℚ) (weight : Source → ℚ) : Option Source → ℚ
  | none => 1-rate
  | some point => rate*weight point

def windowTicketWeightProgram (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  (windowTicketCounts squaredWidth cutoff bits ((windowIndexEquiv cutoff).symm point) : ℚ)/
    (2 : ℚ)^(windowTicketBits cutoff bits)

/-- Every component is executable: the root marginal uses the integer
convolution DP, the other source atoms use Gaussian tickets, and the two
optional-attachment probabilities are exact rational population ratios. -/
def actualBodyBlurProgram (constant n : ℕ) (point : ActualBodyProgramSample constant n) : ℚ :=
  actualRootMarginalProgram n point.1 *
    (optionalWeightProgram (actualLegRateProgram n)
      (windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n) point.2.1 *
    optionalWeightProgram (actualQueueRateProgram n)
      (windowTicketWeightProgram (actualAuxiliarySquaredWidth 1 n) (n^2-1) n) point.2.2)

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance bodyBlurProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualBodyProgramEquiv (constant n : ℕ) : ActualBodyProgramSample constant n≃bodySample (constant : ℝ) n :=
  (Equiv.refl _).prodCongr ((Equiv.optionCongr (actualLegWindowEquiv constant n)).prodCongr (Equiv.refl _))

theorem actualBodyProgramEquiv_apply (constant n : ℕ) (point : ActualBodyProgramSample constant n) :
    actualBodyProgramEquiv constant n point=(point.1,Option.map (actualLegWindowEquiv constant n) point.2.1,point.2.2) := rfl

theorem actualLegRateProgram_cast (n : ℕ) : (actualLegRateProgram n : ℝ)=legRate n := by
  simp only [actualLegRateProgram,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,
    actualRootPopulationProgram_eq,legRate,Parameters.legs,Parameters.security,Nat.cast_pow]

theorem actualQueueRateProgram_cast (n : ℕ) : (actualQueueRateProgram n : ℝ)=queueRate n := by
  simp only [actualQueueRateProgram,Rat.cast_div,Rat.cast_natCast,ParameterProgram.modulus_value,
    actualRootPopulationProgram_eq,queueRate]

theorem windowTicketWeightProgram_cast (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    (windowTicketWeightProgram squaredWidth cutoff bits point : ℝ)=
      (windowTicketLaw squaredWidth cutoff bits).weight point := by
  rw [windowTicketLaw_weight]
  simp only [windowTicketWeightProgram,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]

theorem actualLegTicketLaw_program_weight (constant scale n bits : ℕ)
    (point : Window (actualLegCutoffProgram constant n-1)) :
    (actualLegTicketLaw constant scale n bits).weight (actualLegWindowEquiv constant n point)=
      (windowTicketWeightProgram (actualAuxiliarySquaredWidth scale n)
        (actualLegCutoffProgram constant n-1) bits point : ℝ) := by
  unfold actualLegTicketLaw
  rw [FiniteDist.map_equiv_weight,Equiv.symm_apply_apply,windowTicketWeightProgram_cast]

/-- The finite probability law represented by the rational program. Its
root-normalizer positivity is supplied by the already proved actual
acceptance lower bound, uniformly for all sufficiently large n. -/
def actualBodyBlurApproxLaw (constant n : ℕ)
    (hroot : 0<RootSlice.sumProbability (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n) 0) :
    FiniteDist (bodySample (constant : ℝ) n) :=
  (RootSlice.marginalLaw (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n)
    (Parameters.bodies_positive n) hroot).prod
      (((actualLegTicketLaw constant 10 n n).optional (legRate n) (by unfold legRate; positivity)
        ((body_rates_le_quarter n).1.trans (by norm_num))).prod
      ((actualQueueTicketLaw n n).optional (queueRate n) (by unfold queueRate; positivity)
        ((body_rates_le_quarter n).2.trans (by norm_num))))

theorem actualBodyBlurProgram_cast (constant n : ℕ)
    (hroot : 0<RootSlice.sumProbability (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n) 0)
    (point : ActualBodyProgramSample constant n) :
    (actualBodyBlurProgram constant n point : ℝ)=
      (actualBodyBlurApproxLaw constant n hroot).weight (actualBodyProgramEquiv constant n point) := by
  have hr : (actualRootMarginalProgram n point.1 : ℝ)=
      (RootSlice.marginalLaw (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n)
        (Parameters.bodies_positive n) hroot).weight point.1 := by
    unfold actualRootMarginalProgram
    rw [actualRootPopulationProgram_eq,actualRootTicketMarginal_exact n _ (Parameters.bodies_positive n) hroot]
  rcases point with ⟨root,leg,queue⟩
  cases leg <;> cases queue <;>
    simp only [actualBodyBlurProgram,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,optionalWeightProgram,
      actualBodyBlurApproxLaw,FiniteDist.prod_weight,actualBodyProgramEquiv_apply,
      Option.map_none,Option.map_some,
      FiniteDist.optional_none,FiniteDist.optional_some,actualLegRateProgram_cast,
      actualQueueRateProgram_cast,actualLegTicketLaw_program_weight,windowTicketWeightProgram_cast,
      actualQueueTicketLaw,hr]

private theorem optional_l1 {Source : Type*} [Fintype Source]
    (first second : FiniteDist Source) (rate : ℝ) (h0 : 0≤rate) (h1 : rate≤1) :
    (∑ point,|((first.optional rate h0 h1).weight point)-((second.optional rate h0 h1).weight point)|)≤
      ∑ point,|first.weight point-second.weight point| := by
  rw [Fintype.sum_option]
  simp only [FiniteDist.optional_none,FiniteDist.optional_some,sub_self,abs_zero,zero_add,
    ← mul_sub,abs_mul,abs_of_nonneg h0,← Finset.mul_sum]
  exact mul_le_of_le_one_left (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) h1

def actualBodyBlurProgramError (n : ℕ) : ℝ :=
  6*(n : ℝ)^2*actualRootMarginalError n+2/(2 : ℝ)^n

theorem actualBodyBlurProgramError_negligible : Negligible actualBodyBlurProgramError := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n
    simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  convert ((actualRootMarginalError_negligible.mul_polynomial 2).const_mul 6).add (hm.const_mul 2) using 1
  funext n
  unfold actualBodyBlurProgramError
  ring

/-- All numerical hypotheses are discharged: the computed table converges
in L1 to the physical root-plus-optional-leg-plus-optional-queue body law. -/
theorem actual_body_blur_program_eventually (constant : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ point : ActualBodyProgramSample constant n,
        |(actualBodyBlurProgram constant n point : ℝ)-
          (bodyBlur (constant : ℝ) n).weight (actualBodyProgramEquiv constant n point)|)≤
        actualBodyBlurProgramError n := by
  filter_upwards [actual_root_ticket_acceptance_eventually,actual_root_marginal_program_eventually,
    eventually_ge_atTop 2] with n hroot hm hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hp : 0<RootSlice.sumProbability (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n) 0 :=
    (by positivity : (0 : ℝ)<1/(n : ℝ)^32).trans_le hroot
  have hr (point : Window (v7RootCutoff n)) :
      |(RootSlice.marginalLaw (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n)
        (Parameters.bodies_positive n) hp).weight point-
        (rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n) (Parameters.bodies_positive n)).weight point|≤
      actualRootMarginalError n := by
    have hh := hm point
    unfold actualRootMarginalProgram at hh
    rwa [actualRootPopulationProgram_eq,actualRootTicketMarginal_exact n _ (Parameters.bodies_positive n) hp] at hh
  have hcard : (Fintype.card (Window (v7RootCutoff n)) : ℝ)≤6*(n : ℝ)^2 := by
    rw [← Fintype.card_congr (windowIndexEquiv _),Fintype.card_fin]
    unfold v7RootCutoff
    have hh : 2*(3*n^2-1)+1≤6*n^2 := by
      have h2 : 4≤n^2 := by nlinarith
      omega
    exact_mod_cast hh
  have hrall : (∑ point,|(RootSlice.marginalLaw (actualRootTicketLaw n n) (fun point => (point : ℤ))
      (Parameters.bodies n) (Parameters.bodies_positive n) hp).weight point-
      (rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n) (Parameters.bodies_positive n)).weight point|)≤
      6*(n : ℝ)^2*actualRootMarginalError n := by
    apply (Finset.sum_le_sum (fun point _ => hr point)).trans
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by unfold actualRootMarginalError; positivity)
  have hleg := (optional_l1 (actualLegTicketLaw constant 10 n n)
    (windowGaussian (10*n) (legCutoff (constant : ℝ) n-1)) (legRate n)
    (by unfold legRate; positivity) ((body_rates_le_quarter n).1.trans (by norm_num))).trans
      (by simpa only [Nat.cast_ofNat] using actualLegTicketLaw_l1 constant 10 n n (by decide) (by omega))
  have hqueue := (optional_l1 (actualQueueTicketLaw n n) (windowGaussian n (queueCutoff n))
    (queueRate n) (by unfold queueRate; positivity) ((body_rates_le_quarter n).2.trans (by norm_num))).trans
      (actualQueueTicketLaw_l1 n n (by omega))
  have hextra := (FiniteDist.l1_prod_le _ _ _ _).trans (add_le_add hleg hqueue)
  have htotal := (FiniteDist.l1_prod_le _ _ _ _).trans (add_le_add hrall hextra)
  have heq : (∑ point : ActualBodyProgramSample constant n,|(actualBodyBlurProgram constant n point : ℝ)-
      (bodyBlur (constant : ℝ) n).weight (actualBodyProgramEquiv constant n point)|)=
      ∑ point,|(actualBodyBlurApproxLaw constant n hp).weight point-(bodyBlur (constant : ℝ) n).weight point| := by
    simp only [actualBodyBlurProgram_cast constant n hp]
    convert (actualBodyProgramEquiv constant n).sum_comp (fun point =>
      |(actualBodyBlurApproxLaw constant n hp).weight point-(bodyBlur (constant : ℝ) n).weight point|) using 1
  rw [heq]
  exact htotal.trans_eq (by unfold actualBodyBlurProgramError; ring)

end
end AFT.V7Calibration

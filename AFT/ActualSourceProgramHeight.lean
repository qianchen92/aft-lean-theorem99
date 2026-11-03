import AFT.ActualPairSourceProgram
import AFT.RationalHeight

/-! # Binary heights of the actual numerical root, body, and pair source tables -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance sourceProgramHeightFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem dyadic_ratio_height (tickets bits : ℕ) (h : tickets≤2^bits) :
    HeightBound ((tickets : ℚ)/(2 : ℚ)^bits) (2*bits) := by
  have hn := HeightBound.of_nat h
  have hd : HeightBound ((2 : ℚ)^bits) bits := by
    convert HeightBound.of_nat (le_rfl : 2^bits≤2^bits) using 1
    simp only [Nat.cast_pow,Nat.cast_ofNat]
  convert hn.div hd using 1
  ring

theorem actualRootTicketProbability_height (n count : ℕ) (hn : 2≤n)
    (hcount : count≤Parameters.bodies n) (target : ℤ) :
    HeightBound (actualRootTicketProbability n count target) (32*n^62) := by
  have hN : count≤2*n^60 := by
    apply hcount.trans
    apply (Nat.sub_le _ _).trans
    simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  have hlookup : integerLookup (actualRootTicketConvolution n count).data ((3*n^2-1)*count) target≤
      2^(actualRootTicketBits n n*count) := by
    unfold integerLookup
    split_ifs
    · have hh := run_nat_le_total (2*(3*n^2-1)) (actualRootTicketCounts n n) count (target+(((3*n^2-1)*count : ℕ) : ℤ)).toNat
      rw [actualRootTicketCounts_sum,←pow_mul] at hh
      exact hh
    · exact Nat.zero_le _
  have hh := dyadic_ratio_height _ _ hlookup
  apply hh.mono
  have hb := actualRootTicketBits_bound n hn
  calc
    _ ≤ 2*((8*n^2)*(2*n^60)) := by gcongr
    _ = _ := by ring

theorem actualRootMarginalProgram_height (n : ℕ) (hn : 2≤n) (point : Window (3*n^2-1)) :
    HeightBound (actualRootMarginalProgram n point) (80*n^62) := by
  have hcount : actualRootTicketCounts n n ((windowIndexEquiv _).symm point)≤2^(actualRootTicketBits n n) := by
    rw [←actualRootTicketCounts_sum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hscalar := dyadic_ratio_height _ _ hcount
  have hscalar' : HeightBound ((actualRootTicketCounts n n ((windowIndexEquiv _).symm point) : ℚ)/(2 : ℚ)^actualRootTicketBits n n) (16*n^2) := by
    apply hscalar.mono
    have hh := actualRootTicketBits_bound n hn
    omega
  have hremain := actualRootTicketProbability_height n (Parameters.bodies n-1) hn (Nat.sub_le _ _) (-(point : ℤ))
  have hfull := actualRootTicketProbability_height n (Parameters.bodies n) hn le_rfl 0
  unfold actualRootMarginalProgram actualRootTicketMarginal
  rw [actualRootPopulationProgram_eq]
  apply ((hscalar'.mul hremain).div hfull).mono
  have hp := Nat.pow_le_pow_right (by omega : 1≤n) (show 2≤62 by decide)
  omega

theorem windowTicketWeightProgram_height (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    HeightBound (windowTicketWeightProgram squaredWidth cutoff bits point) (2*windowTicketBits cutoff bits) := by
  apply dyadic_ratio_height
  rw [←windowTicketCounts_sum squaredWidth cutoff bits]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)

theorem actualLegRateProgram_height (n : ℕ) (hn : 2≤n) :
    HeightBound (actualLegRateProgram n) (3*n^60) := by
  have hN : actualRootPopulationProgram n≤2*n^60 := by
    rw [actualRootPopulationProgram_eq]
    apply (Nat.sub_le _ _).trans
    simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  unfold actualLegRateProgram
  rw [max_eq_right hn]
  have hnum := (HeightBound.nat_coarse n).pow 30
  apply (hnum.div (HeightBound.nat_coarse _)).mono
  have hlarge : 30≤n^59 := by
    have hh := Nat.pow_le_pow_left hn 59
    norm_num at hh
    omega
  have hsmall : n*30≤n^60 := by
    calc
      _ ≤ n*n^59 := Nat.mul_le_mul_left n hlarge
      _ = _ := by ring
  omega

theorem actualQueueRateProgram_height (n : ℕ) (hn : 2≤n) :
    HeightBound (actualQueueRateProgram n) (4*n^60) := by
  have hN : actualRootPopulationProgram n≤2*n^60 := by
    rw [actualRootPopulationProgram_eq]
    apply (Nat.sub_le _ _).trans
    simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  have hq : (ParameterProgram.modulus n).value≤2*n^40 := by
    rw [ParameterProgram.modulus_value]
    simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2
  apply ((HeightBound.nat_coarse _).div (HeightBound.nat_coarse _)).mono
  have hp := Nat.pow_le_pow_right (by omega : 1≤n) (show 40≤60 by decide)
  omega

theorem optionalWeightProgram_height {Source : Type*} (rate : ℚ) (weight : Source → ℚ)
    (rateBits weightBits : ℕ) (hrate : HeightBound rate rateBits)
    (hweight : ∀ point,HeightBound (weight point) weightBits) (point : Option Source) :
    HeightBound (optionalWeightProgram rate weight point) (rateBits+weightBits+1) := by
  cases point with
  | none =>
    change HeightBound (1-rate) _
    rw [sub_eq_add_neg]
    apply (HeightBound.one.add hrate.neg).mono
    omega
  | some point => exact (hrate.mul (hweight point)).mono (by omega)

def actualBodyProgramHeight (constant n : ℕ) : ℕ := 80*n^62+7*n^60+2+(4*constant+12)*n^2

def actualPairProgramHeight (constant n : ℕ) : ℕ := actualBodyProgramHeight constant n+(4*constant+4)*n^2

theorem actualBodyBlurProgram_height (constant n : ℕ) (hn : 2≤n) (point : ActualBodyProgramSample constant n) :
    HeightBound (actualBodyBlurProgram constant n point) (actualBodyProgramHeight constant n) := by
  have hleg : ∀ p,HeightBound
      (windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n p)
      ((4*constant+4)*n^2) := by
    intro p
    apply (windowTicketWeightProgram_height _ _ _ p).mono
    have hh := actualLegTicketBits_bound constant n hn
    change 2*actualLegTicketBits constant n n≤_
    nlinarith
  have hqueue : ∀ p,HeightBound (windowTicketWeightProgram (actualAuxiliarySquaredWidth 1 n) (n^2-1) n p) (8*n^2) := by
    intro p
    apply (windowTicketWeightProgram_height _ _ _ p).mono
    have hh := actualQueueTicketBits_bound n hn
    change 2*actualQueueTicketBits n n≤_
    omega
  have hlegOption := optionalWeightProgram_height _ _ _ _ (actualLegRateProgram_height n hn) hleg point.2.1
  have hqueueOption := optionalWeightProgram_height _ _ _ _ (actualQueueRateProgram_height n hn) hqueue point.2.2
  convert (actualRootMarginalProgram_height n hn point.1).mul (hlegOption.mul hqueueOption) using 1
  unfold actualBodyProgramHeight
  ring

theorem actualPairSourceProgram_height (constant n : ℕ) (hn : 2≤n) (point : ActualPairProgramSample constant n) :
    HeightBound (actualPairSourceProgram constant n point) (actualPairProgramHeight constant n) := by
  have hleg := windowTicketWeightProgram_height (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n point.2
  have hleg' : HeightBound (windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n point.2)
      ((4*constant+4)*n^2) := by
    apply hleg.mono
    have hh := actualLegTicketBits_bound constant n hn
    change 2*actualLegTicketBits constant n n≤_
    nlinarith
  exact (actualBodyBlurProgram_height constant n hn point.1).mul hleg'

end
end AFT.V7Calibration

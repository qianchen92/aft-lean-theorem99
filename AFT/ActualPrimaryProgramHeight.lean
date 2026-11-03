import AFT.ActualResponseProgramHeight

/-! # Actual primary-program rational heights, including the sampled beta -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem actual_modulus_program_le (n : ℕ) (hn : 2≤n) :
    (ParameterProgram.modulus n).value≤2*n^40 := by
  rw [ParameterProgram.modulus_value]
  simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2

theorem actual_dimension_program_le (n : ℕ) (hn : 2≤n) :
    actualDimensionProgram n≤2*n^60 := by
  rw [actualDimensionProgram_eq]
  simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2

theorem actual_root_population_program_le (n : ℕ) (hn : 2≤n) :
    actualRootPopulationProgram n≤2*n^60 := by
  rw [actualRootPopulationProgram_eq]
  have hp := Parameters.population_identity n
  have hd : Parameters.dimension n≤2*n^60 := by
    simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2
  omega

def actualBodyMeanProgramHeight (constant n : ℕ) : ℕ :=
  pairProgramCardBudget constant n*(actualBodyProgramHeight constant n+2*n^40+1)

theorem actualBodyMeanProgram_height (constant n : ℕ) (hn : 2≤n) (color : ℤ) :
    HeightBound (actualBodyMeanProgram constant n color) (actualBodyMeanProgramHeight constant n) := by
  have hsize : actualSafeSizeProgram n≤2*n^40 :=
    (Nat.sub_le _ _).trans (actual_modulus_program_le n hn)
  have hc : Fintype.card (ActualBodyProgramSample constant n)≤pairProgramCardBudget constant n := by
    have hh := actualPairProgram_card_le constant n hn
    have hw : Fintype.card (Window (actualLegCutoffProgram constant n-1))=
        2*(actualLegCutoffProgram constant n-1)+1 := by
      rw [←Fintype.card_congr (windowIndexEquiv _),Fintype.card_fin]
    change Fintype.card (ActualBodyProgramSample constant n ×
      Window (actualLegCutoffProgram constant n-1))≤_ at hh
    rw [Fintype.card_prod,hw] at hh
    nlinarith
  let term := fun sample : ActualBodyProgramSample constant n =>
    actualBodyBlurProgram constant n sample*
      intervalProbabilityProgram (actualSafeMarginProgram n) (actualSafeSizeProgram n)
        (color-actualBodyShiftProgram constant n sample)
  have ht (sample : ActualBodyProgramSample constant n) :
      HeightBound (term sample) (actualBodyProgramHeight constant n+2*n^40) :=
    (actualBodyBlurProgram_height constant n hn sample).mul
      ((intervalProbabilityProgram_height _ _ _).mono hsize)
  change HeightBound (∑sample,term sample) _
  apply (HeightBound.sum Finset.univ term _ (fun sample _ => ht sample)).mono
  simpa only [Finset.card_univ] using Nat.mul_le_mul_right _ hc

def actualFairSliceProgramHeight (constant n : ℕ) : ℕ :=
  2*actualMixedSliceProgramHeight constant n+3

theorem actualFairSliceProgram_height (constant n : ℕ) (hn : 2≤n) (shifted : Bool) (color : ℤ) :
    HeightBound (actualFairSliceProgram constant n shifted color) (actualFairSliceProgramHeight constant n) := by
  have hh := ((actualMixedSliceProgram_height constant n hn true shifted color).add
    (actualMixedSliceProgram_height constant n hn false shifted color)).div (HeightBound.nat_coarse 2)
  convert hh using 1
  unfold actualFairSliceProgramHeight
  ring

def actualBasePrimaryProgramHeight (constant n : ℕ) : ℕ :=
  actualActivationProgramHeight constant n+4*n^60+2*n^30+2*n^40+
    2*actualBodyMeanProgramHeight constant n+2*actualFairSliceProgramHeight constant n+8

theorem actualBasePrimaryProgram_height (constant n : ℕ) (hn : 2≤n) (color : ℤ) :
    HeightBound (actualBasePrimaryProgram constant n color) (actualBasePrimaryProgramHeight constant n) := by
  have hdim := (HeightBound.nat_coarse (actualDimensionProgram n)).mono (actual_dimension_program_le n hn)
  have hroot := (HeightBound.nat_coarse (actualRootPopulationProgram n)).mono (actual_root_population_program_le n hn)
  have hq := (HeightBound.nat_coarse (ParameterProgram.modulus n).value).mono (actual_modulus_program_le n hn)
  have hleg : HeightBound (actualLegPopulationProgram n : ℚ) (n^30) := by
    simpa only [actualLegPopulationProgram,max_eq_right hn] using HeightBound.nat_coarse (n^30)
  have hbody := actualBodyMeanProgram_height constant n hn color
  have hs (shifted : Bool) := (HeightBound.nat_coarse 2).mul (actualFairSliceProgram_height constant n hn shifted color)
  have hfirst := rational_sub_height _ _ _ _ (hdim.div (hleg.mul hq)) ((hroot.div hleg).mul hbody)
  have hsecond := rational_sub_height _ _ _ _ hfirst (hs true)
  have hthird := ((actualActivationInverseApprox_height constant n hn).mul hsecond).add (hs false)
  have hh := rational_sub_height _ _ _ _ hthird hbody
  convert hh using 1
  unfold actualBasePrimaryProgramHeight
  ring

def actualBoundaryCoefficientProgramHeight (constant n betaBits : ℕ) : ℕ :=
  4*(constant+24)*n^2+4*n^40+betaBits+2*n^60+n^30+2

theorem actualBoundaryCoefficientProgram_height (constant n : ℕ) (hn : 2≤n)
    (beta : ℚ) (betaBits : ℕ) (hb : HeightBound beta betaBits) (color : ℤ) :
    HeightBound (actualBoundaryCoefficientProgram constant n beta color)
      (actualBoundaryCoefficientProgramHeight constant n betaBits) := by
  have hbc : actualBoundaryCountProgram constant n≤2*(constant+24)*n^2 := by
    unfold actualBoundaryCountProgram
    have hh := actualBoundaryHalfProgram_abs constant n hn
    have ht : (actualBoundaryHalfProgram constant n).toNat≤(actualBoundaryHalfProgram constant n).natAbs := by omega
    nlinarith
  have hic : actualInteriorCountProgram constant n≤2*n^40 :=
    (Nat.sub_le _ _).trans (actual_modulus_program_le n hn)
  have hboundary := (HeightBound.nat_coarse (actualBoundaryCountProgram constant n)).mono hbc
  have hinterior := (HeightBound.nat_coarse (actualInteriorCountProgram constant n)).mono hic
  have hq := (HeightBound.nat_coarse (ParameterProgram.modulus n).value).mono (actual_modulus_program_le n hn)
  have hdim := (HeightBound.nat_coarse (actualDimensionProgram n)).mono (actual_dimension_program_le n hn)
  have hleg : HeightBound (actualLegPopulationProgram n : ℚ) (n^30) := by
    simpa only [actualLegPopulationProgram,max_eq_right hn] using HeightBound.nat_coarse (n^30)
  have hbu : HeightBound (actualBoundaryUniformProgram constant n color) (2*(constant+24)*n^2) := by
    unfold actualBoundaryUniformProgram
    split_ifs
    · exact hboundary.inv
    · exact HeightBound.zero.mono (Nat.zero_le _)
  have hiu : HeightBound (actualInteriorUniformProgram constant n color) (2*n^40) := by
    unfold actualInteriorUniformProgram
    split_ifs
    · exact HeightBound.zero.mono (Nat.zero_le _)
    · exact hinterior.inv
  have hh := ((hboundary.div hq).mul (rational_sub_height _ _ _ _ hb.inv (hdim.div hleg))).mul
    (rational_sub_height _ _ _ _ hbu hiu)
  convert hh using 1
  unfold actualBoundaryCoefficientProgramHeight
  ring

def actualPrimaryProgramHeight (constant n betaBits : ℕ) : ℕ :=
  actualBasePrimaryProgramHeight constant n+actualActivationProgramHeight constant n+
    actualBoundaryCoefficientProgramHeight constant n betaBits+1

theorem actualPrimaryProgram_height (constant n : ℕ) (hn : 2≤n)
    (beta : ℚ) (betaBits : ℕ) (hb : HeightBound beta betaBits) (color : ℤ) :
    HeightBound (actualPrimaryProgram constant n beta color) (actualPrimaryProgramHeight constant n betaBits) := by
  have hh := (actualBasePrimaryProgram_height constant n hn color).add
    ((actualActivationInverseApprox_height constant n hn).mul
      (actualBoundaryCoefficientProgram_height constant n hn beta betaBits hb color))
  convert hh using 1
  unfold actualPrimaryProgramHeight
  ring

end
end AFT.V7Calibration

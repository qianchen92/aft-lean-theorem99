import AFT.ActualSourceProgramHeight
import AFT.ActualAuxiliaryProgramHeight
import AFT.ActualRankInverseProgram

/-! # Polynomial rational heights of the actual response and preconditioner -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance responseHeightFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem rational_sub_height (first second : ℚ) (firstBits secondBits : ℕ)
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first-second) (firstBits+secondBits+1) := by
  simpa only [sub_eq_add_neg] using hf.add hs.neg

def pairProgramCardBudget (constant n : ℕ) : ℕ := 96*(constant+1)^2*n^8

theorem actualPairProgram_card_le (constant n : ℕ) (hn : 2≤n) :
    Fintype.card (ActualPairProgramSample constant n)≤pairProgramCardBudget constant n := by
  have hwindow (cutoff : ℕ) : Fintype.card (Window cutoff)=2*cutoff+1 := by
    rw [←Fintype.card_congr (windowIndexEquiv cutoff),Fintype.card_fin]
  have hc := actualLegCutoffProgram_le constant n
  have hpow : 1≤n^2 := by nlinarith
  have hr : Fintype.card (Window (3*n^2-1))≤6*n^2 := by rw [hwindow];omega
  have hl : Fintype.card (Window (actualLegCutoffProgram constant n-1))≤(2*constant+1)*n^2 := by rw [hwindow];nlinarith [Nat.sub_le (actualLegCutoffProgram constant n) 1]
  have hlo : Fintype.card (Option (Window (actualLegCutoffProgram constant n-1)))≤(2*constant+2)*n^2 := by rw [Fintype.card_option];nlinarith
  have hqo : Fintype.card (Option (Window (n^2-1)))≤4*n^2 := by rw [Fintype.card_option,hwindow];omega
  simp only [ActualPairProgramSample,ActualBodyProgramSample,Fintype.card_prod]
  calc
    _ ≤ (6*n^2)*((2*constant+2)*n^2*(4*n^2))*((2*constant+1)*n^2) := by gcongr
    _ ≤ (6*n^2)*((2*constant+2)*n^2*(4*n^2))*((2*constant+2)*n^2) := by gcongr;omega
    _ = _ := by unfold pairProgramCardBudget;ring

theorem intervalProbabilityProgram_height (start : ℤ) (width : ℕ) (point : ℤ) :
    HeightBound (intervalProbabilityProgram start width point) width := by
  unfold intervalProbabilityProgram
  split_ifs
  · exact (HeightBound.nat_coarse width).inv
  · exact HeightBound.zero.mono (Nat.zero_le _)

theorem publicAnchorKernelProgram_height (modulus width color : ℕ) (output : ℤ) :
    HeightBound (publicAnchorKernelProgram modulus width color output) (2*width+3) := by
  have hh := ((intervalProbabilityProgram_height (publicAnchorStartProgram modulus width color true) width output).add
    (intervalProbabilityProgram_height (publicAnchorStartProgram modulus width color false) width output)).div (HeightBound.nat_coarse 2)
  convert hh using 1
  ring

def actualAnchorProgramHeight (constant n : ℕ) : ℕ :=
  pairProgramCardBudget constant n*(actualPairProgramHeight constant n+2*n^32+4)

theorem actualAnchorProgram_height (constant n : ℕ) (hn : 2≤n) (rootOnly : Bool) (input : ℕ) (output : ℤ) :
    HeightBound (actualAnchorProgram constant n rootOnly input output) (actualAnchorProgramHeight constant n) := by
  have hw : actualAnchorWidthProgram n=n^32 := by simp only [actualAnchorWidthProgram,max_eq_right hn]
  let term := fun sample : ActualPairProgramSample constant n =>
    actualPairSourceProgram constant n sample *
      publicAnchorKernelProgram (ParameterProgram.modulus n).value (actualAnchorWidthProgram n) input
        (output-(if rootOnly then sample.1.1.val else actualBodyShiftProgram constant n sample.1))
  have ht (sample : ActualPairProgramSample constant n) :
      HeightBound (term sample) (actualPairProgramHeight constant n+(2*n^32+3)) := by
    have hk := publicAnchorKernelProgram_height (ParameterProgram.modulus n).value (actualAnchorWidthProgram n) input
      (output-(if rootOnly then sample.1.1.val else actualBodyShiftProgram constant n sample.1))
    rw [hw] at hk
    dsimp only [term]
    rw [hw]
    exact (actualPairSourceProgram_height constant n hn sample).mul hk
  change HeightBound (∑ sample,term sample) _
  apply (HeightBound.sum Finset.univ term _ (fun sample _ => ht sample)).mono
  simp only [Finset.card_univ]
  unfold actualAnchorProgramHeight
  apply Nat.mul_le_mul (actualPairProgram_card_le constant n hn)
  omega

theorem sliceProbabilityProgram_height (modulus boundary shift color : ℤ) :
    HeightBound (sliceProbabilityProgram modulus boundary shift color) (modulus.toNat+2*boundary.natAbs) := by
  have hc : (TrimmedSlice.slice modulus boundary shift).card ≤ modulus.toNat+2*boundary.natAbs := by
    rw [TrimmedSlice.slice_card]
    have hm := Int.self_le_toNat modulus
    have hb : -((boundary.natAbs : ℕ) : ℤ)≤boundary := by rw [Int.natCast_natAbs];exact neg_abs_le _
    have ht := abs_nonneg shift
    omega
  unfold sliceProbabilityProgram
  split_ifs
  · exact (HeightBound.nat_coarse _).inv.mono hc
  · exact HeightBound.zero.mono (Nat.zero_le _)

theorem actualBoundaryHalfProgram_abs (constant n : ℕ) (hn : 2≤n) :
    (actualBoundaryHalfProgram constant n).natAbs≤(constant+24)*n^2 := by
  unfold actualBoundaryHalfProgram
  apply (Int.natAbs_sub_le _ _).trans
  simp only [Int.natAbs_natCast,actualSafeMarginProgram,max_eq_right hn]
  have hc := actualLegCutoffProgram_le constant n
  nlinarith [Nat.sub_le (3*n^2) 1,Nat.sub_le (actualLegCutoffProgram constant n) 1,Nat.sub_le (n^2) 1]

def actualSliceAtomProgramHeight (constant n : ℕ) : ℕ := 2*n^40+2*(constant+24)*n^2

def actualMixedSliceProgramHeight (constant n : ℕ) : ℕ :=
  pairProgramCardBudget constant n*(actualPairProgramHeight constant n+
    n^32*(n^32+actualSliceAtomProgramHeight constant n+1)+1)

theorem averagedSliceProgram_height (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    HeightBound (averagedSliceProgram modulus boundary start source width color)
      (width*(width+(modulus.toNat+2*boundary.natAbs)+1)) := by
  have hh := HeightBound.sum (anchorInterval start width) _ (width+(modulus.toNat+2*boundary.natAbs))
    (fun shift _ => (intervalProbabilityProgram_height start width shift).mul
      (sliceProbabilityProgram_height modulus boundary (shift-source) color))
  simpa only [anchorInterval_card] using hh

theorem actualMixedSliceProgram_height (constant n : ℕ) (hn : 2≤n) (positive shifted : Bool) (color : ℤ) :
    HeightBound (actualMixedSliceProgram constant n positive shifted color) (actualMixedSliceProgramHeight constant n) := by
  have hw : actualAnchorWidthProgram n=n^32 := by simp only [actualAnchorWidthProgram,max_eq_right hn]
  have hq : (ParameterProgram.modulus n).value≤2*n^40 := by
    rw [ParameterProgram.modulus_value]
    simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2
  have hb := actualBoundaryHalfProgram_abs constant n hn
  have hk (sample : ActualPairProgramSample constant n) :
      HeightBound (averagedSliceProgram (ParameterProgram.modulus n).value (actualBoundaryHalfProgram constant n)
        (actualPairStartProgram constant n positive sample) (if shifted then sample.2.val else 0)
        (actualAnchorWidthProgram n) color)
        (n^32*(n^32+actualSliceAtomProgramHeight constant n+1)) := by
    apply (averagedSliceProgram_height _ _ _ _ _ _).mono
    rw [hw,Int.toNat_natCast]
    unfold actualSliceAtomProgramHeight
    apply Nat.mul_le_mul_left
    nlinarith
  have hh := HeightBound.sum Finset.univ _
    (actualPairProgramHeight constant n+n^32*(n^32+actualSliceAtomProgramHeight constant n+1))
    (fun sample _ => (actualPairSourceProgram_height constant n hn sample).mul (hk sample))
  apply hh.mono
  simp only [Finset.card_univ]
  exact Nat.mul_le_mul_right _ (actualPairProgram_card_le constant n hn)

def actualNormalizedSignProgramHeight (constant n : ℕ) : ℕ :=
  actualActivationProgramHeight constant n+4*actualMixedSliceProgramHeight constant n+3

theorem actualNormalizedSignProgram_height (constant n : ℕ) (hn : 2≤n) (output : ℤ) :
    HeightBound (actualNormalizedSignProgram constant n output) (actualNormalizedSignProgramHeight constant n) := by
  have hd (shifted : Bool) := rational_sub_height _ _ _ _
    (actualMixedSliceProgram_height constant n hn true shifted output)
    (actualMixedSliceProgram_height constant n hn false shifted output)
  have hh := rational_sub_height _ _ _ _ ((actualActivationInverseApprox_height constant n hn).mul (hd true)) (hd false)
  convert hh using 1
  unfold actualNormalizedSignProgramHeight
  ring

theorem paletteSignProgram_height (modulus color : ℕ) : HeightBound (paletteSignProgram modulus color) 0 := by
  unfold paletteSignProgram
  split_ifs
  · exact HeightBound.one.neg
  · exact HeightBound.one
  · exact HeightBound.zero

def actualRankDenominatorProgramHeight (constant n : ℕ) : ℕ :=
  2*n^40*(actualNormalizedSignProgramHeight constant n+1)+1

def actualRankInverseProgramHeight (constant n : ℕ) : ℕ :=
  actualRankDenominatorProgramHeight constant n+actualNormalizedSignProgramHeight constant n+1

theorem actualRankDenominatorProgram_height (constant n : ℕ) (hn : 2≤n) :
    HeightBound (actualRankDenominatorProgram constant n) (actualRankDenominatorProgramHeight constant n) := by
  have hq : (ParameterProgram.modulus n).value≤2*n^40 := by
    rw [ParameterProgram.modulus_value]
    simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2
  have hh := HeightBound.sum (Finset.range (ParameterProgram.modulus n).value) _
    (actualNormalizedSignProgramHeight constant n) (by
      intro color _
      simpa only [zero_add] using (paletteSignProgram_height (ParameterProgram.modulus n).value color).mul
        (actualNormalizedSignProgram_height constant n hn color))
  apply (HeightBound.one.add hh).mono
  simp only [Finset.card_range,zero_add]
  unfold actualRankDenominatorProgramHeight
  gcongr

theorem actualRankInverseProgram_height (constant n input output : ℕ) (hn : 2≤n) :
    HeightBound (actualRankInverseProgram constant n input output) (actualRankInverseProgramHeight constant n) := by
  have hid : HeightBound (if input=output then (1 : ℚ) else 0) 0 := by
    split_ifs
    · exact HeightBound.one
    · exact HeightBound.zero
  have hh := ((actualRankDenominatorProgram_height constant n hn).inv.mul
    (actualNormalizedSignProgram_height constant n hn output)).mul
      (paletteSignProgram_height (ParameterProgram.modulus n).value input)
  convert rational_sub_height _ _ _ _ hid hh using 1
  unfold actualRankInverseProgramHeight
  omega

end
end AFT.V7Calibration

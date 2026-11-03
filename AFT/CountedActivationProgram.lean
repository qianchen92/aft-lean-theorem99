import AFT.CountedRootMarginal

/-! # Actual finite cutoff and activation evaluators with operation counts -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators

/-- The fixed eighth and ninth powers use bounded repeated multiplication;
the integer comparison table is evaluated once. -/
def countedLegCutoff (constant n : ℕ) : BetaReference.CountedNatural :=
  let threshold := (BetaReference.CountedInteger.power (constant : ℤ) 8).value*
    (BetaReference.CountedInteger.power (n : ℤ) 9).value
  let accepted := (Finset.range (constant*n^2+1)).filter (fun index : ℕ =>
    (BetaReference.CountedInteger.power (index : ℤ) 8).value<threshold)
  ⟨accepted.card,12*(constant*n^2+1)+25⟩

theorem countedLegCutoff_value (constant n : ℕ) :
    (countedLegCutoff constant n).value=actualLegCutoffProgram constant n := by
  simp only [countedLegCutoff,BetaReference.CountedInteger.power_value]
  have he (index : ℕ) : (index : ℤ)^8<(constant : ℤ)^8*(n : ℤ)^9 ↔ index^8<constant^8*n^9 := by
    exact_mod_cast (Iff.rfl : index^8<constant^8*n^9 ↔ index^8<constant^8*n^9)
  simp only [he]
  rfl

/-- Cached public scalar weights are queried at the actual zero atom. -/
def countedActivation (constant n : ℕ) : GaussianArithmetic :=
  let cutoff := countedLegCutoff constant n
  let width := actualLegCutoffProgram constant n-1
  let first := countedWindowWeights (actualAuxiliarySquaredWidth 1 n) width (n+1)
  let second := countedWindowWeights (actualAuxiliarySquaredWidth 10 n) width (n+1)
  let zero : Fin (2*width+1) := ⟨width,by omega⟩
  ⟨1/(100*((2*actualLegCutoffProgram constant n-1 : ℕ) : ℚ)^2)*(first.value.get zero*second.value.get zero),
    cutoff.work+first.work+second.work+15⟩

def countedActivationInverse (constant n : ℕ) : GaussianArithmetic :=
  let activation := countedActivation constant n
  ⟨activation.value⁻¹,activation.work+1⟩

theorem countedActivation_value (constant n : ℕ) :
    (countedActivation constant n).value=actualActivationApprox constant n n := by
  have hz (width : ℕ) : windowIndexEquiv width ⟨width,by omega⟩=windowZero width := by
    apply Subtype.ext
    simp [windowIndexEquiv,windowZero]
  simp only [countedActivation,countedWindowWeights_value,
    windowGaussianWeights,hz,actualActivationApprox,actualLegZeroApprox,actualFeatureCountProgram,Nat.cast_pow]
  rfl

theorem countedActivationInverse_value (constant n : ℕ) :
    (countedActivationInverse constant n).value=actualActivationInverseApprox constant n n := by
  simp only [countedActivationInverse,countedActivation_value,actualActivationInverseApprox]

def activationQueryWork (constant n : ℕ) : ℕ :=
  12*(constant*n^2+1)+41+2*windowQueryWork (constant*n^2) n

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem actualAuxiliarySquaredWidth_ge_one (scale n : ℕ) (hs : 1≤scale) (hn : 1≤n) :
    (1 : ℚ)≤actualAuxiliarySquaredWidth scale n := by
  have hnq : (1 : ℚ)≤n := by exact_mod_cast hn
  have hsq : (1 : ℚ)≤scale := by exact_mod_cast hs
  unfold actualAuxiliarySquaredWidth
  have hh : (1 : ℚ)≤scale*n := by nlinarith
  nlinarith

theorem countedActivationInverse_work (constant n : ℕ) (hn : 1≤n) :
    (countedActivationInverse constant n).work≤activationQueryWork constant n := by
  have hc : actualLegCutoffProgram constant n-1≤constant*n^2 := by
    exact (Nat.sub_le _ _).trans (actualLegCutoffProgram_le constant n)
  let width := actualLegCutoffProgram constant n-1
  have hfirst := countedWindowTicketWeight_work (actualAuxiliarySquaredWidth 1 n) width n
    (actualAuxiliarySquaredWidth_ge_one 1 n (by decide) hn) (windowZero width)
  have hsecond := countedWindowTicketWeight_work (actualAuxiliarySquaredWidth 10 n) width n
    (actualAuxiliarySquaredWidth_ge_one 10 n (by decide) hn) (windowZero width)
  simp only [countedWindowTicketWeight,countedWindowTickets,GaussianArithmetic.power_work,PermutationProgram.powerTwo_work] at hfirst hsecond
  have hm := windowQueryWork_mono hc (le_refl n)
  change windowQueryWork width n≤windowQueryWork (constant*n^2) n at hm
  simp only [countedActivationInverse,countedActivation]
  change 12*(constant*n^2+1)+25+(countedWindowWeights (actualAuxiliarySquaredWidth 1 n) width (n+1)).work+
    (countedWindowWeights (actualAuxiliarySquaredWidth 10 n) width (n+1)).work+15+1≤_
  unfold activationQueryWork
  omega

theorem countedActivation_work (constant n : ℕ) (hn : 1≤n) :
    (countedActivation constant n).work≤activationQueryWork constant n := by
  have hh := countedActivationInverse_work constant n hn
  change (countedActivation constant n).work+1≤_ at hh
  omega

end
end AFT.V7Calibration

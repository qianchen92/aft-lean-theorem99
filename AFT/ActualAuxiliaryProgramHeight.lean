import AFT.GaussianWindowHeight
import AFT.ActualActivationProgram

/-! # Actual auxiliary Gaussian and activation operand heights -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def auxiliaryHeightBudget (constant scale n : ℕ) : ℕ := (constant+scale+10)^2*n^4

theorem auxiliaryHeightBudget_bounds (constant scale n : ℕ) (hn : 2≤n) :
    2≤auxiliaryHeightBudget constant scale n ∧ constant*n^2≤auxiliaryHeightBudget constant scale n ∧
      (scale*n)^2≤auxiliaryHeightBudget constant scale n ∧ n+1≤auxiliaryHeightBudget constant scale n ∧
      constant^2*n^4≤auxiliaryHeightBudget constant scale n := by
  have hq : 1≤constant+scale+10 := by omega
  have hs : 1≤(constant+scale+10)^2 := Nat.one_le_pow _ _ hq
  have hbase : constant+scale+10≤(constant+scale+10)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq (show 1≤2 by decide)
  have hc : constant≤(constant+scale+10)^2 := (by omega : constant≤constant+scale+10).trans hbase
  have hss : scale^2≤(constant+scale+10)^2 := Nat.pow_le_pow_left (by omega : scale≤constant+scale+10) _
  have hcc : constant^2≤(constant+scale+10)^2 := Nat.pow_le_pow_left (by omega : constant≤constant+scale+10) _
  have hn24 : n^2≤n^4 := Nat.pow_le_pow_right (by omega : 1≤n) (by decide)
  have hnplus : n+1≤n^2 := by nlinarith
  unfold auxiliaryHeightBudget
  refine ⟨?_,?_,?_,?_,Nat.mul_le_mul_right _ hcc⟩
  · nlinarith
  · exact Nat.mul_le_mul hc hn24
  · calc
      _ = scale^2*n^2 := by ring
      _ ≤ _ := Nat.mul_le_mul hss hn24
  · nlinarith

theorem actual_auxiliary_ratio_height_bounds (constant scale n : ℕ) (hs : 1≤scale) (hn : 2≤n)
    (point : Window (actualLegCutoffProgram constant n-1)) :
    0≤gaussianRatio (actualAuxiliarySquaredWidth scale n) point ∧
      gaussianRatio (actualAuxiliarySquaredWidth scale n) point≤auxiliaryHeightBudget constant scale n ∧
      HeightBound (gaussianRatio (actualAuxiliarySquaredWidth scale n) point)
        (3*auxiliaryHeightBudget constant scale n) := by
  let budget := auxiliaryHeightBudget constant scale n
  have hb := auxiliaryHeightBudget_bounds constant scale n hn
  have hcut : actualLegCutoffProgram constant n-1≤constant*n^2 := (Nat.sub_le _ _).trans (actualLegCutoffProgram_le constant n)
  have hp := Finset.mem_Icc.mp point.property
  have habs : point.val.natAbs≤constant*n^2 := by
    have hcutInt : ((actualLegCutoffProgram constant n-1 : ℕ) : ℤ)≤((constant*n^2 : ℕ) : ℤ) := by exact_mod_cast hcut
    have hh : |point.val|≤((constant*n^2 : ℕ) : ℤ) := abs_le.mpr
      ⟨(neg_le_neg hcutInt).trans hp.1,hp.2.trans hcutInt⟩
    rw [←Nat.cast_le (α := ℤ),Int.natCast_natAbs]
    exact hh
  have hnum : (point.val : ℚ)^2≤(budget : ℚ) := by
    have hsq : point.val.natAbs^2≤constant^2*n^4 := by
      calc
        _ ≤ (constant*n^2)^2 := Nat.pow_le_pow_left habs _
        _ = _ := by ring
    have hh := hsq.trans hb.2.2.2.2
    have heq : ((point.val.natAbs^2 : ℕ) : ℚ)=(point.val : ℚ)^2 := by
      push_cast
      rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,sq_abs]
    rw [←heq]
    exact_mod_cast hh
  have hwidth : (1 : ℚ)≤actualAuxiliarySquaredWidth scale n := by
    unfold actualAuxiliarySquaredWidth
    have hsn : (1 : ℚ)≤scale*n := by exact_mod_cast (show 1≤scale*n by nlinarith)
    nlinarith
  have hwidthHeight : HeightBound (actualAuxiliarySquaredWidth scale n) budget := by
    have hh := (HeightBound.nat_coarse ((scale*n)^2)).mono hb.2.2.1
    simpa only [actualAuxiliarySquaredWidth,Nat.cast_pow,Nat.cast_mul] using hh
  have hz : HeightBound (point.val : ℚ) budget := HeightBound.of_int
    ((habs.trans hb.2.1).trans (Nat.lt_two_pow_self (n := budget)).le)
  refine ⟨by unfold gaussianRatio;positivity,?_,?_⟩
  · unfold gaussianRatio
    exact (div_le_self (sq_nonneg _) hwidth).trans hnum
  · convert (hz.pow 2).div hwidthHeight using 1
    ring

theorem actualLegZeroApprox_height (constant scale n : ℕ) (hs : 1≤scale) (hn : 2≤n) :
    HeightBound (actualLegZeroApprox constant scale n (n+1))
      (500000000*(auxiliaryHeightBudget constant scale n)^6) := by
  have hb := auxiliaryHeightBudget_bounds constant scale n hn
  apply windowApproxWeight_height_of_budget _ _ _ _ hb.1
    ((Nat.sub_le _ _).trans ((actualLegCutoffProgram_le constant n).trans hb.2.1)) hb.2.2.2.1
  · intro point
    exact (actual_auxiliary_ratio_height_bounds constant scale n hs hn point).1
  · intro point
    exact (actual_auxiliary_ratio_height_bounds constant scale n hs hn point).2.1
  · intro point
    exact (actual_auxiliary_ratio_height_bounds constant scale n hs hn point).2.2

def actualActivationProgramHeight (constant n : ℕ) : ℕ :=
  400*constant^2*n^4+500000000*(auxiliaryHeightBudget constant 1 n)^6+
    500000000*(auxiliaryHeightBudget constant 10 n)^6

theorem actualActivationApprox_height (constant n : ℕ) (hn : 2≤n) :
    HeightBound (actualActivationApprox constant n n) (actualActivationProgramHeight constant n) := by
  have hfeature : 100*actualFeatureCountProgram constant n≤400*constant^2*n^4 := by
    have hc := actualLegCutoffProgram_le constant n
    unfold actualFeatureCountProgram
    calc
      _ ≤ 100*(2*actualLegCutoffProgram constant n)^2 := by gcongr;omega
      _ ≤ 100*(2*(constant*n^2))^2 := by gcongr
      _ = _ := by ring
  have hden : HeightBound (100*(actualFeatureCountProgram constant n : ℚ)) (400*constant^2*n^4) := by
    have hh := (HeightBound.nat_coarse (100*actualFeatureCountProgram constant n)).mono hfeature
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  have hh := (HeightBound.one.div hden).mul
    ((actualLegZeroApprox_height constant 1 n (by decide) hn).mul (actualLegZeroApprox_height constant 10 n (by decide) hn))
  convert hh using 1
  unfold actualActivationProgramHeight
  omega

theorem actualActivationInverseApprox_height (constant n : ℕ) (hn : 2≤n) :
    HeightBound (actualActivationInverseApprox constant n n) (actualActivationProgramHeight constant n) :=
  (actualActivationApprox_height constant n hn).inv

end
end AFT.V7Calibration

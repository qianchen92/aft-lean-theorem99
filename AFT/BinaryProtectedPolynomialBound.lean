import AFT.BinaryProtectedPolynomials
import AFT.ActualChartProgramHeight

/-! Polynomial bit work of the complete protected sampler. -/
namespace AFT.BinaryArithmetic
open Polynomial RationalBits AFT.BoundaryCalibration AFT.V7Calibration

set_option maxHeartbeats 800000 in
theorem protectedMetadataWork_mono {c d q r b e s t : ℕ}
    (hc : c ≤ d) (hq : q ≤ r) (hb : b ≤ e) (hs : s ≤ t) :
    protectedMetadataWork c q b s ≤ protectedMetadataWork d r e t := by
  unfold protectedMetadataWork protectedMetadataCoreWork protectedDimensionsWork
    protectedFeatureWork modularDifferenceWork protectedPaletteWork protectedScaleWork supportWork
  gcongr

theorem protectedAtomWork_mono {c d : ℕ} (hc : c ≤ d) :
    protectedAtomWork c ≤ protectedAtomWork d := by
  unfold protectedAtomWork protectedAtomHeight primitiveWorkBound
  gcongr

theorem protectedChartWeightWork_mono {c d q r b e s t k l : ℕ}
    (hc : c ≤ d) (hq : q ≤ r) (hb : b ≤ e) (hs : s ≤ t) (hk : k ≤ l) :
    protectedChartWeightWork c q b s k ≤ protectedChartWeightWork d r e t l := by
  have hm := protectedMetadataWork_mono hc hq hb hs
  have ha := protectedAtomWork_mono hc
  have hw := markedChartWork_mono (Nat.mul_le_mul hq (Nat.mul_le_mul hq hq)) hq
    (show (2*c+1)*(2*c+1) ≤ (2*d+1)*(2*d+1) by gcongr)
    (show protectedAtomHeight c ≤ protectedAtomHeight d by unfold protectedAtomHeight;gcongr) hk
  unfold protectedChartWeightWork
  gcongr

theorem protectedChartWeightHeight_mono {c d q r k l : ℕ}
    (hc : c ≤ d) (hq : q ≤ r) (hk : k ≤ l) :
    protectedChartWeightHeight c q k ≤ protectedChartWeightHeight d r l := by
  apply chartWeightHeight_mono (by gcongr) hq (by gcongr) _ hk
  unfold protectedAtomHeight
  gcongr

theorem binarySafeProtectedChartWork_mono {c d q r b e s t k l i j : ℕ}
    (hc : c ≤ d) (hq : q ≤ r) (hb : b ≤ e) (hs : s ≤ t) (hk : k ≤ l) (hi : i ≤ j) :
    binarySafeProtectedChartWork c q b s k i ≤ binarySafeProtectedChartWork d r e t l j := by
  have hm := protectedMetadataWork_mono hc hq hb hs
  have hw := protectedChartWeightWork_mono hc hq hb hs hk
  have hh := protectedChartWeightHeight_mono hc hq hk
  have hd := binaryPositiveDrawWork_mono (Nat.mul_le_mul hq (Nat.mul_le_mul hq hq)) hh hi
  unfold binarySafeProtectedChartWork binaryProtectedChartDrawWork
  gcongr

theorem binarySafeProtectedChartDraw_polynomial_work (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool)
    (mark : Fin modulus) (steps bits : ℕ)
    (word : Fin (bits+modulus*(modulus*modulus)+1) → Fin 2)
    (cutoffBound modulusBound boundaryBound baselineBound stepsBound bitsBound : Polynomial ℕ)
    (n : ℕ) (hc : cutoff ≤ cutoffBound.eval n) (hq : modulus ≤ modulusBound.eval n)
    (hb : boundary.length ≤ boundaryBound.eval n) (hs : baseline.length ≤ baselineBound.eval n)
    (hk : steps ≤ stepsBound.eval n) (hi : bits ≤ bitsBound.eval n) :
    (binarySafeProtectedChartDraw cutoff modulus boundarySign baselineSign boundary baseline mark steps bits word).work ≤
      (binarySafeProtectedChartWorkPolynomial cutoffBound modulusBound boundaryBound baselineBound stepsBound bitsBound).eval n := by
  rw [binarySafeProtectedChartWorkPolynomial_eval]
  exact (binarySafeProtectedChartDraw_work cutoff modulus boundarySign baselineSign boundary baseline mark steps bits word).trans
    (binarySafeProtectedChartWork_mono hc hq hb hs hk hi)

noncomputable def binaryActualChartPolynomial (constant : ℕ) (boundaryBits baselineBits : Polynomial ℕ) : Polynomial ℕ :=
  binarySafeProtectedChartWorkPolynomial (C constant*X^2) (2*X^40) boundaryBits baselineBits X X

theorem binaryActualChart_polynomial_work (constant n : ℕ) (hn : 2 ≤ n)
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool)
    (mark : Fin (chartProgramModulus n))
    (word : Fin (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2)
    (boundaryBits baselineBits : Polynomial ℕ)
    (hb : boundary.length ≤ boundaryBits.eval n) (hs : baseline.length ≤ baselineBits.eval n) :
    (binarySafeProtectedChartDraw (chartProgramCutoff constant n) (chartProgramModulus n)
      boundarySign baselineSign boundary baseline mark n n word).work ≤
      (binaryActualChartPolynomial constant boundaryBits baselineBits).eval n := by
  apply binarySafeProtectedChartDraw_polynomial_work _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ hb hs
    (by simp) (by simp)
  · simpa only [eval_mul,eval_C,eval_pow,eval_X] using
      ((Nat.sub_le (actualLegCutoffProgram constant n) 1).trans (actualLegCutoffProgram_le constant n))
  · simpa only [eval_mul,eval_ofNat,eval_pow,eval_X] using (actual_chart_array_bounds constant n hn).1

end AFT.BinaryArithmetic

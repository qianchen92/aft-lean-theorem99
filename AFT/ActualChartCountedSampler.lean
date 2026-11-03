import AFT.ActualChartArithmeticBounds
import AFT.CountedMarkedChartSampler

/-! # The actual chart dyadic program, with its complete rational-arithmetic count -/
namespace AFT.BoundaryCalibration
open RationalNumerics V7Calibration BetaReference
open scoped BigOperators

def actualCountedChartTicket (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n))
    (word : Fin (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2) : CountedNatural :=
  let cutoff := chartProgramCutoff constant n
  let modulus := chartProgramModulus n
  let feature := finiteProtectedFeatures cutoff modulus
  let allowed := finiteProtectedPalettes cutoff modulus boundary baseline
  countedMarkedChartFinDraw (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) feature allowed
    (finiteMarkedSafe feature (finiteAffineScale modulus) allowed)
    (finiteMarkedFiber feature (finiteAffineScale modulus) allowed (finiteProtectedMark cutoff) mark)
    (finiteProtectedMark cutoff) (finiteProtectedAtom cutoff) n n word

 theorem actualCountedChartTicket_value (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n))
    (word : Fin (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2) :
    (actualCountedChartTicket constant n boundary baseline mark word).value=
      (actualFiniteAffineChartDraw constant n boundary baseline mark n n word).val := by
  exact countedMarkedChartFinDraw_value _ _ _ _ _ _ _ _ _ _ _ _

 def actualChartSamplingWorkBound (constant n : ℕ) : ℕ :=
   actualChartArithmeticWorkBound constant n+3*n+14*actualChartCountBound n+5

 theorem actualCountedChartTicket_work (constant n : ℕ) (hn : 2≤n) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n))
    (word : Fin (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2) :
    (actualCountedChartTicket constant n boundary baseline mark word).work≤actualChartSamplingWorkBound constant n := by
  have hh := countedMarkedChartFinDraw_work
    (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)) (chartProgramModulus n)
    ((2*chartProgramCutoff constant n+1)*(2*chartProgramCutoff constant n+1))
    (finiteProtectedFeatures (chartProgramCutoff constant n) (chartProgramModulus n))
    (finiteProtectedPalettes (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline)
    (finiteMarkedSafe (finiteProtectedFeatures (chartProgramCutoff constant n) (chartProgramModulus n))
      (finiteAffineScale (chartProgramModulus n))
      (finiteProtectedPalettes (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline))
    (finiteMarkedFiber (finiteProtectedFeatures (chartProgramCutoff constant n) (chartProgramModulus n))
      (finiteAffineScale (chartProgramModulus n))
      (finiteProtectedPalettes (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline)
      (finiteProtectedMark (chartProgramCutoff constant n)) mark)
    (finiteProtectedMark (chartProgramCutoff constant n)) (finiteProtectedAtom (chartProgramCutoff constant n)) n n word
  apply hh.trans
  have hb := actual_chart_array_bounds constant n hn
  have hw := chartArithmeticWork_mono hb.2.1 hb.1 hb.2.2 (le_rfl : n≤n)
  unfold actualChartSamplingWorkBound actualChartArithmeticWorkBound
  omega

end AFT.BoundaryCalibration

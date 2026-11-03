import AFT.CountedChartProgram
import AFT.ActualChartProgramHeight
import AFT.RationalPositiveNormalizeHeight

/-! # Actual chart setup arithmetic and final rational operand bounds -/
namespace AFT.BoundaryCalibration
open RationalNumerics V7Calibration
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- This is a polynomial in `n` for every fixed cutoff constant. It includes
matrix setup, defect setup, both stored iterations, and the final weights. -/
def actualChartArithmeticWorkBound (constant n : ℕ) : ℕ :=
  chartArithmeticWork (actualChartCountBound n) (2*n^40) (actualChartFeatureBound constant n) n

 theorem chartArithmeticWork_mono {charts charts' colors colors' features features' steps steps' : ℕ}
    (hc : charts≤charts') (hq : colors≤colors') (hf : features≤features') (hs : steps≤steps') :
    chartArithmeticWork charts colors features steps≤chartArithmeticWork charts' colors' features' steps' := by
  unfold chartArithmeticWork ChartArithmetic.projectionWork ChartArithmetic.featureWork cachedIterationWork
  gcongr

 theorem actual_chart_rational_work (constant n : ℕ) (hn : 2≤n)
    (boundary baseline : ℤ) (mark : Fin (chartProgramModulus n)) :
    let cutoff := chartProgramCutoff constant n
    let modulus := chartProgramModulus n
    let feature := finiteProtectedFeatures cutoff modulus
    let allowed := finiteProtectedPalettes cutoff modulus boundary baseline
    (countedMarkedChartWeightProgram (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1))
      feature allowed (finiteMarkedSafe feature (finiteAffineScale modulus) allowed)
      (finiteMarkedFiber feature (finiteAffineScale modulus) allowed (finiteProtectedMark cutoff) mark)
      (finiteProtectedMark cutoff) (finiteProtectedAtom cutoff) n).work≤actualChartArithmeticWorkBound constant n := by
  dsimp only
  apply (countedMarkedChartWeightProgram_work _ _ _ _ _ _ _ _ _ _).trans
  have hb := actual_chart_array_bounds constant n hn
  exact chartArithmeticWork_mono hb.2.1 hb.1 hb.2.2 le_rfl

/-- Normalization on any nonempty finite array; the zero branch is a literal
index-zero fallback and requires no choice procedure. -/
def chartPositiveWeight (charts : ℕ) [NeZero charts] (raw : Fin charts → ℚ) (index : Fin charts) : ℚ :=
  let total := ∑ point,max 0 (raw point)
  if total=0 then (if index=0 then 1 else 0) else max 0 (raw index)/total

 theorem chartPositiveWeight_succ (count : ℕ) (raw : Fin (count+1) → ℚ) :
    chartPositiveWeight (count+1) raw=positiveWeightProgram raw := rfl

 theorem chartPositiveWeight_height (charts : ℕ) [NeZero charts] (raw : Fin charts → ℚ)
    (bits : ℕ) (hraw : ∀ point,HeightBound (raw point) bits) (point : Fin charts) :
    HeightBound (chartPositiveWeight charts raw point) (bits+charts*(bits+1)) := by
  cases charts with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ count => exact positiveWeightProgram_height raw bits hraw point

 def actualChartRawWeight (constant n : ℕ) (boundary baseline : ℤ) (mark : Fin (chartProgramModulus n)) :
    Vector ℚ (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)) :=
  let cutoff := chartProgramCutoff constant n
  let modulus := chartProgramModulus n
  let feature := finiteProtectedFeatures cutoff modulus
  let allowed := finiteProtectedPalettes cutoff modulus boundary baseline
  markedChartWeightProgram (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) feature allowed
    (finiteMarkedSafe feature (finiteAffineScale modulus) allowed)
    (finiteMarkedFiber feature (finiteAffineScale modulus) allowed (finiteProtectedMark cutoff) mark)
    (finiteProtectedMark cutoff) (finiteProtectedAtom cutoff) n

 def actualChartNormalizedWeight (constant n : ℕ) (boundary baseline : ℤ) (mark : Fin (chartProgramModulus n)) :
    Fin (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)) → ℚ :=
   chartPositiveWeight _ (actualChartRawWeight constant n boundary baseline mark).get

 def actualChartNormalizedHeight (constant n : ℕ) : ℕ :=
   actualChartWeightHeight constant n+actualChartCountBound n*(actualChartWeightHeight constant n+1)
 def actualChartTicketOperandHeight (constant n : ℕ) : ℕ :=
   n+actualChartCountBound n+1+actualChartNormalizedHeight constant n

 theorem actual_chart_normalized_height (constant n : ℕ) (hn : 2≤n)
    (boundary baseline : ℤ) (mark : Fin (chartProgramModulus n))
    (point : Fin (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n))) :
    HeightBound (actualChartNormalizedWeight constant n boundary baseline mark point) (actualChartNormalizedHeight constant n) := by
  have hraw (point : Fin (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n))) :
      HeightBound ((actualChartRawWeight constant n boundary baseline mark).get point) (actualChartWeightHeight constant n) := by
    exact actual_chart_raw_weight_height constant n hn boundary baseline mark n le_rfl point
  have hh := chartPositiveWeight_height _ (actualChartRawWeight constant n boundary baseline mark).get
    (actualChartWeightHeight constant n) hraw point
  change HeightBound (chartPositiveWeight _ (actualChartRawWeight constant n boundary baseline mark).get point) _
  apply hh.mono
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (actual_chart_array_bounds constant n hn).2.1) _

 theorem actual_chart_ticket_operand_height (constant n : ℕ) (hn : 2≤n)
    (boundary baseline : ℤ) (mark : Fin (chartProgramModulus n))
    (point : Fin (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n))) :
    HeightBound ((2 : ℚ)^(n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1)*
      actualChartNormalizedWeight constant n boundary baseline mark point) (actualChartTicketOperandHeight constant n) := by
  have ht : HeightBound ((2 : ℚ)^(n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1))
      (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using HeightBound.of_nat (le_rfl :
      2^(n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1)≤
      2^(n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1))
  apply (ht.mul (actual_chart_normalized_height constant n hn boundary baseline mark point)).mono
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left
    (actual_chart_array_bounds constant n hn).2.1 n) 1) _

 theorem actual_chart_ticket_operand_binary_size (constant n : ℕ) (hn : 2≤n)
    (boundary baseline : ℤ) (mark : Fin (chartProgramModulus n))
    (point : Fin (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n))) :
    let value := (2 : ℚ)^(n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1)*
      actualChartNormalizedWeight constant n boundary baseline mark point
    value.num.natAbs.size≤actualChartTicketOperandHeight constant n+1 ∧
    value.den.size≤actualChartTicketOperandHeight constant n+1 :=
  (actual_chart_ticket_operand_height constant n hn boundary baseline mark point).binary_size

end AFT.BoundaryCalibration

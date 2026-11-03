import AFT.CountedPrimarySources

/-! # A counted evaluator for the actual calibrated primary probability

Scalar tables are cached before the complete shared-source expectations.
The integer slice length is evaluated by its proved closed formula, so a
slice query needs no enumeration of its entire color interval.
-/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators

/-- Two integer comparisons and the reciprocal of the integer width. -/
def countedIntervalProbability (start : ℤ) (width : ℕ) (point : ℤ) : GaussianArithmetic :=
  ⟨if start≤point ∧ point<start+width then (width : ℚ)⁻¹ else 0,5⟩

/-- Both endpoint tests and the exact nonnegative interval length. -/
def countedSliceProbability (modulus boundary shift color : ℤ) : GaussianArithmetic :=
  ⟨if boundary+max shift 0≤color ∧ color < modulus-boundary+min shift 0
    then ((modulus-2*boundary-|shift|).toNat : ℚ)⁻¹ else 0,12⟩

theorem countedIntervalProbability_value (start : ℤ) (width : ℕ) (point : ℤ) :
    (countedIntervalProbability start width point).value=intervalProbabilityProgram start width point := by
  simp only [countedIntervalProbability,intervalProbabilityProgram,anchorInterval,Finset.mem_Ico]

theorem countedSliceProbability_value (modulus boundary shift color : ℤ) :
    (countedSliceProbability modulus boundary shift color).value=sliceProbabilityProgram modulus boundary shift color := by
  unfold sliceProbabilityProgram
  rw [TrimmedSlice.slice_card]
  simp only [countedSliceProbability,TrimmedSlice.slice,Finset.mem_Ico]

def countedAverageSlice (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) : GaussianArithmetic :=
  let result := GaussianArithmetic.sum (anchorInterval start width) (fun shift =>
    (countedIntervalProbability start width shift).mul (countedSliceProbability modulus boundary (shift-source) color))
  ⟨result.value,result.work+3*width+5⟩

theorem countedAverageSlice_value (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    (countedAverageSlice modulus boundary start source width color).value=averagedSliceProgram modulus boundary start source width color := by
  simp only [countedAverageSlice,GaussianArithmetic.sum,GaussianArithmetic.mul,
    countedIntervalProbability_value,countedSliceProbability_value,averagedSliceProgram]

theorem countedAverageSlice_work (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    (countedAverageSlice modulus boundary start source width color).work=22*width+5 := by
  simp only [countedAverageSlice,GaussianArithmetic.sum,GaussianArithmetic.mul,
    countedIntervalProbability,countedSliceProbability,Finset.sum_const,anchorInterval_card,smul_eq_mul]
  omega

def primaryTableBodyMean {constant n : ℕ} (table : PrimarySourceTable constant n) (color : ℤ) : GaussianArithmetic :=
  let result := GaussianArithmetic.sum Finset.univ (fun sample : ActualBodyProgramSample constant n =>
    (primaryTableBodyWeight table sample).mul
      (countedIntervalProbability table.margin (table.modulus-2*table.margin)
        (color-actualBodyShiftProgram constant n sample)))
  ⟨result.value,result.work+15*Fintype.card (ActualBodyProgramSample constant n)+10⟩

def primaryTableMixedSlice {constant n : ℕ} (table : PrimarySourceTable constant n)
    (positive shifted : Bool) (color : ℤ) : GaussianArithmetic :=
  let result := GaussianArithmetic.sum Finset.univ (fun sample : ActualPairProgramSample constant n =>
    let start := (if positive then (table.width : ℤ) else -2*(table.width : ℤ)+1)+actualBodyShiftProgram constant n sample.1
    (primaryTablePairWeight table sample).mul
      (countedAverageSlice table.modulus table.boundary start
        (if shifted then sample.2.val else 0) table.width color))
  ⟨result.value,result.work+20*Fintype.card (ActualPairProgramSample constant n)+10⟩

def primaryTableFairSlice {constant n : ℕ} (table : PrimarySourceTable constant n)
    (shifted : Bool) (color : ℤ) : GaussianArithmetic :=
  ((primaryTableMixedSlice table true shifted color).add
    (primaryTableMixedSlice table false shifted color)).div (.literal 2)

def primaryTableBoundaryCoefficient {constant n : ℕ} (table : PrimarySourceTable constant n)
    (beta : ℚ) (color : ℤ) : GaussianArithmetic :=
  let boundaryCount := 2*table.boundary.toNat
  let interiorCount := table.modulus-boundaryCount
  let outside := color < table.boundary ∨ (table.modulus : ℤ)-1-table.boundary<color
  let boundary := if outside then (boundaryCount : ℚ)⁻¹ else 0
  let interior := if outside then 0 else (interiorCount : ℚ)⁻¹
  ⟨((boundaryCount : ℚ)/table.modulus)*(beta⁻¹-(table.dimension : ℚ)/table.legs)*(boundary-interior),30⟩

/-- All five expensive subcomputations are evaluated once. The final scalar
formula uses their stored values, including the same activation in the beta repair. -/
def countedPrimaryProgram (constant n : ℕ) (beta : ℚ) (color : ℤ) : GaussianArithmetic :=
  let table := countedPrimarySources constant n
  let activation := countedActivationInverse constant n
  let body := primaryTableBodyMean table color
  let shifted := primaryTableFairSlice table true color
  let unshifted := primaryTableFairSlice table false color
  let boundary := primaryTableBoundaryCoefficient table beta color
  ⟨activation.value*((table.dimension : ℚ)/((table.legs : ℚ)*table.modulus)-
      (table.population : ℚ)/table.legs*body.value-2*shifted.value)+2*unshifted.value-body.value+
      activation.value*boundary.value,
    table.work+activation.work+body.work+shifted.work+unshifted.work+boundary.work+30⟩

def countedPrimaryFromBits (constant n : ℕ) (word : Fin (n+n) → Fin 2) (color : ℤ) : GaussianArithmetic :=
  let beta := ParameterProgram.beta n word
  let primary := countedPrimaryProgram constant n beta.value color
  ⟨primary.value,primary.work+beta.work⟩

theorem primaryTableBodyMean_value (constant n : ℕ) (color : ℤ) :
    (primaryTableBodyMean (countedPrimarySources constant n) color).value=actualBodyMeanProgram constant n color := by
  simp only [primaryTableBodyMean,GaussianArithmetic.sum,GaussianArithmetic.mul,
    primaryTableBodyWeight_value,countedIntervalProbability_value,countedPrimarySources_margin,
    countedPrimarySources_modulus,actualBodyMeanProgram,actualSafeSizeProgram]

theorem primaryTableMixedSlice_value (constant n : ℕ) (positive shifted : Bool) (color : ℤ) :
    (primaryTableMixedSlice (countedPrimarySources constant n) positive shifted color).value=
      actualMixedSliceProgram constant n positive shifted color := by
  simp only [primaryTableMixedSlice,GaussianArithmetic.sum,GaussianArithmetic.mul,
    primaryTablePairWeight_value,countedAverageSlice_value,countedPrimarySources_modulus,
    countedPrimarySources_boundary,countedPrimarySources_width,actualMixedSliceProgram,actualPairStartProgram]

theorem primaryTableFairSlice_value (constant n : ℕ) (shifted : Bool) (color : ℤ) :
    (primaryTableFairSlice (countedPrimarySources constant n) shifted color).value=actualFairSliceProgram constant n shifted color := by
  simp only [primaryTableFairSlice,GaussianArithmetic.add,GaussianArithmetic.div,GaussianArithmetic.literal,
    primaryTableMixedSlice_value,actualFairSliceProgram]

theorem primaryTableBoundaryCoefficient_value (constant n : ℕ) (beta : ℚ) (color : ℤ) :
    (primaryTableBoundaryCoefficient (countedPrimarySources constant n) beta color).value=
      actualBoundaryCoefficientProgram constant n beta color := by
  simp only [primaryTableBoundaryCoefficient,countedPrimarySources_boundary,countedPrimarySources_modulus,
    countedPrimarySources_dimension,countedPrimarySources_legs,actualBoundaryCoefficientProgram,
    actualBoundaryCountProgram,actualInteriorCountProgram,actualBoundaryUniformProgram,actualInteriorUniformProgram]

theorem countedPrimaryProgram_value (constant n : ℕ) (beta : ℚ) (color : ℤ) :
    (countedPrimaryProgram constant n beta color).value=actualPrimaryProgram constant n beta color := by
  simp only [countedPrimaryProgram,countedActivationInverse_value,primaryTableBodyMean_value,
    primaryTableFairSlice_value,primaryTableBoundaryCoefficient_value,countedPrimarySources_dimension,
    countedPrimarySources_legs,countedPrimarySources_modulus,countedPrimarySources_population,
    actualPrimaryProgram,actualBasePrimaryProgram]

theorem countedPrimaryFromBits_value (constant n : ℕ) (word : Fin (n+n) → Fin 2) (color : ℤ) :
    (countedPrimaryFromBits constant n word color).value=actualPrimaryFromBits constant n word color := by
  simp only [countedPrimaryFromBits,countedPrimaryProgram_value,actualPrimaryFromBits]

def primaryQueryWork (constant n : ℕ) : ℕ := primarySourcesWork constant n+activationQueryWork constant n+
  38*pairProgramCardBudget constant n+4*(pairProgramCardBudget constant n*(22*n^32+46)+10)+100

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem actualBodyProgram_card_le (constant n : ℕ) (hn : 2≤n) :
    Fintype.card (ActualBodyProgramSample constant n)≤pairProgramCardBudget constant n := by
  have hh := actualPairProgram_card_le constant n hn
  change Fintype.card (ActualBodyProgramSample constant n ×Window (actualLegCutoffProgram constant n-1))≤_ at hh
  rw [Fintype.card_prod,←Fintype.card_congr (windowIndexEquiv _),Fintype.card_fin] at hh
  nlinarith

theorem primaryTableBodyMean_work {constant n : ℕ} (table : PrimarySourceTable constant n) (color : ℤ) :
    (primaryTableBodyMean table color).work=38*Fintype.card (ActualBodyProgramSample constant n)+10 := by
  simp only [primaryTableBodyMean,GaussianArithmetic.sum,GaussianArithmetic.mul,primaryTableBodyWeight_work,
    countedIntervalProbability,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  omega

theorem primaryTableMixedSlice_work {constant n : ℕ} (table : PrimarySourceTable constant n)
    (positive shifted : Bool) (color : ℤ) :
    (primaryTableMixedSlice table positive shifted color).work=
      Fintype.card (ActualPairProgramSample constant n)*(22*table.width+46)+10 := by
  simp only [primaryTableMixedSlice,GaussianArithmetic.sum,GaussianArithmetic.mul,primaryTablePairWeight_work,
    countedAverageSlice_work,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  ring

theorem countedPrimaryProgram_work (constant n : ℕ) (hn : 2≤n) (beta : ℚ) (color : ℤ) :
    (countedPrimaryProgram constant n beta color).work≤primaryQueryWork constant n := by
  have hs := countedPrimarySources_work constant n hn
  have ha := countedActivationInverse_work constant n (by omega)
  have hc := actualBodyProgram_card_le constant n hn
  have hp := actualPairProgram_card_le constant n hn
  simp only [countedPrimaryProgram,primaryTableBodyMean_work,primaryTableFairSlice,
    GaussianArithmetic.div,GaussianArithmetic.add,GaussianArithmetic.literal,primaryTableMixedSlice_work,
    primaryTableBoundaryCoefficient,countedPrimarySources_width,actualAnchorWidthProgram,max_eq_right hn]
  unfold primaryQueryWork
  have hb := Nat.mul_le_mul_left 38 hc
  have hpair := Nat.mul_le_mul_right (22*n^32+46) hp
  omega

theorem countedPrimaryProgram_height (constant n : ℕ) (hn : 2≤n)
    (beta : ℚ) (betaBits : ℕ) (hb : HeightBound beta betaBits) (color : ℤ) :
    HeightBound (countedPrimaryProgram constant n beta color).value (actualPrimaryProgramHeight constant n betaBits) := by
  rw [countedPrimaryProgram_value]
  exact actualPrimaryProgram_height constant n hn beta betaBits hb color

end
end AFT.V7Calibration

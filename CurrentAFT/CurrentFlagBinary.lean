import CurrentAFT.CurrentFlagArray
import AFT.BinaryChartInputsCost

/-!
# Binary-rational simultaneous flag repair

The line mask excludes all protected zero-first-coordinate inputs.  The
deletion matrix and every iterate are stored arrays; the program uses the
existing Boolean-list arithmetic and sequential mask/vector scans.
-/

namespace CurrentAFT.CurrentFlagBinary

open AFT AFT.RationalNumerics AFT.BoundaryCalibration AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators

def defectTerm {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts)
    (point : Fin charts) (index : Fin features) : RationalResult :=
  let onLine := readVector false line index
  if onLine.value then ⟨zero, onLine.work + 2⟩ else
    let term := chartProjectionTerm feature allowed spike point index
    ⟨term.data, onLine.work + term.work + 2⟩

theorem defectTerm_value {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts)
    (point : Fin charts) (index : Fin features) :
    (defectTerm feature allowed line spike point index).data.decode =
      if line.get index then 0 else chartFeatureProgram charts colors (feature.get index).get
        (maskSet (allowed.get index)) (fun input => (spike.get input).decode) point := by
  simp only [defectTerm, readVector_value]
  split <;> simp_all only [zero_value, chartProjectionTerm, readVector_value, chartFeature_value]

def defect {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
  sumFin features (defectTerm feature allowed line spike point)

theorem component_eq (charts colors : ℕ) (feature : Fin charts → Fin colors) (allowed : Finset (Fin colors))
    (profile : Fin charts → ℚ) (point : Fin charts) :
    chartFeatureProgram charts colors feature allowed profile point =
      CurrentFlagArray.component charts feature allowed profile point := by
  simp only [chartFeatureProgram, CurrentFlagArray.component, CurrentFlagArray.conditional,
    CurrentFlagArray.mean, chartConditionalProgram, chartExpectationProgram, Fintype.card_fin]

theorem defect_value {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts) (point : Fin charts) :
    (defect feature allowed line spike point).data.decode =
      CurrentFlagArray.defect charts (fun index => (feature.get index).get)
        (fun index => maskSet (allowed.get index)) line.get (fun input => (spike.get input).decode) point := by
  simp only [defect, sumFin_value, defectTerm_value, component_eq, CurrentFlagArray.defect]

def targetEntry {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (atom : RationalBits) (spike : Vector RationalBits charts)
    (point : Fin charts) : RationalResult :=
  let remaining := difference one atom
  let odds := quotient atom remaining.data
  let offLine := defect feature allowed line spike point
  let correction := multiply odds.data offLine.data
  let result := difference one correction.data
  ⟨result.data, remaining.work + odds.work + offLine.work + correction.work + result.work + 5⟩

theorem targetEntry_value {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (atom : RationalBits) (spike : Vector RationalBits charts)
    (point : Fin charts) :
    (targetEntry feature allowed line atom spike point).data.decode =
      CurrentFlagArray.target charts (fun index => (feature.get index).get)
        (fun index => maskSet (allowed.get index)) line.get atom.decode
        (fun input => (spike.get input).decode) point := by
  simp only [targetEntry, difference_value, quotient_value, RationalBits.multiply_value, one_value,
    defect_value, CurrentFlagArray.target]

def maskedEntry {charts : ℕ} (safe : Vector Bool charts) (profile : Vector RationalBits charts)
    (point : Fin charts) : RationalResult :=
  let active := readVector false safe point
  if active.value then
    let value := readVector zero profile point
    ⟨value.value, active.work + value.work + 2⟩
  else ⟨zero, active.work + 2⟩

theorem maskedEntry_value {charts : ℕ} (safe : Vector Bool charts) (profile : Vector RationalBits charts)
    (point : Fin charts) :
    (maskedEntry safe profile point).data.decode = if safe.get point then (profile.get point).decode else 0 := by
  simp only [maskedEntry, readVector_value]
  split <;> simp_all only [zero_value]

def regular {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (safe fiber : Vector Bool charts) (atom : RationalBits) (steps : ℕ) :
    ArrayResult charts :=
  let spike := buildArray charts (chartSpike fiber)
  let matrix := chartDeletionMatrix feature allowed safe
  let rhs := buildArray charts (targetEntry feature allowed line atom spike.data)
  let raw := iteration matrix.data rhs.data steps
  let result := buildArray charts (maskedEntry safe raw.data)
  ⟨result.data, spike.work + matrix.work + rhs.work + raw.work + result.work + 5⟩

theorem regular_value {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (safe fiber : Vector Bool charts) (atom : RationalBits)
    (steps : ℕ) (point : Fin charts) :
    ((regular feature allowed line safe fiber atom steps).data.get point).decode =
      if safe.get point then
        linearIteration
          (chartDeletionMatrixProgram charts colors features (fun index => (feature.get index).get)
            (fun index => maskSet (allowed.get index)) (maskSet safe))
          (CurrentFlagArray.target charts (fun index => (feature.get index).get)
            (fun index => maskSet (allowed.get index)) line.get atom.decode
            (chartSpikeProgram charts (maskSet fiber))) steps point else 0 := by
  simp only [regular, buildArray_get, maskedEntry_value, iteration_value, chartDeletionMatrix_value,
    targetEntry_value, chartSpike_value]

end CurrentAFT.CurrentFlagBinary

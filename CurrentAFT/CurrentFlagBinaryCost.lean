import CurrentAFT.CurrentFlagBinary

/-! Literal bit-operation and rational-height bounds for all-line flag repair. -/

namespace CurrentAFT.CurrentFlagBinary

open AFT AFT.RationalNumerics AFT.BoundaryCalibration AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1200000

def defectHeight (charts colors features spikeBits : ℕ) : ℕ :=
  features * (chartFeatureHeight charts colors spikeBits + 1)

def targetHeight (charts colors features atomBits spikeBits : ℕ) : ℕ :=
  2 * atomBits + defectHeight charts colors features spikeBits + 2

def defectTermWork (charts colors features spikeBits : ℕ) : ℕ :=
  featureWork charts colors spikeBits + 12 * features + charts + colors + 13

def offLineWork (charts colors features spikeBits : ℕ) : ℕ :=
  finiteSumWork features (chartFeatureHeight charts colors spikeBits)
    (defectTermWork charts colors features spikeBits)

def targetWork (charts colors features atomBits spikeBits : ℕ) : ℕ :=
  offLineWork charts colors features spikeBits +
    7 * primitiveWorkBound (targetHeight charts colors features atomBits spikeBits) + 11

theorem defectTerm_height {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts) (bits : ℕ)
    (hh : ∀ point, HeightBound (spike.get point).decode bits) (point : Fin charts) (index : Fin features) :
    HeightBound (defectTerm feature allowed line spike point index).data.decode
      (chartFeatureHeight charts colors bits) := by
  rw [defectTerm_value]
  split
  · exact HeightBound.zero.mono (Nat.zero_le _)
  · exact chartFeatureProgram_height charts colors bits _ _ _ hh point

theorem defectTerm_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts) (bits : ℕ)
    (hh : ∀ point, HeightBound (spike.get point).decode bits) (point : Fin charts) (index : Fin features) :
    (defectTerm feature allowed line spike point index).work ≤ defectTermWork charts colors features bits := by
  have hl := readVector_work false line index
  have hf := readVector_work (Vector.replicate charts (0 : Fin colors)) feature index
  have ha := readVector_work (Vector.replicate colors false) allowed index
  have hv := chartFeature_work (readVector (Vector.replicate charts 0) feature index).value
    (readVector (Vector.replicate colors false) allowed index).value spike bits hh point
  have hi := index.isLt
  simp only [defectTerm]
  split
  · dsimp only
    unfold defectTermWork
    omega
  · simp only [chartProjectionTerm]
    unfold defectTermWork
    omega

theorem defect_height {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts) (bits : ℕ)
    (hh : ∀ point, HeightBound (spike.get point).decode bits) (point : Fin charts) :
    HeightBound (defect feature allowed line spike point).data.decode (defectHeight charts colors features bits) := by
  simpa only [defect, defectHeight] using
    sumFin_height features (chartFeatureHeight charts colors bits) _ (defectTerm_height feature allowed line spike bits hh point)

theorem defect_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts) (bits : ℕ)
    (hh : ∀ point, HeightBound (spike.get point).decode bits) (point : Fin charts) :
    (defect feature allowed line spike point).work ≤ offLineWork charts colors features bits := by
  exact sumFin_work features (chartFeatureHeight charts colors bits) (defectTermWork charts colors features bits)
    _ (defectTerm_height feature allowed line spike bits hh point) (defectTerm_work feature allowed line spike bits hh point)

theorem targetEntry_height {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (atom : RationalBits) (spike : Vector RationalBits charts)
    (atomBits spikeBits : ℕ) (ha : HeightBound atom.decode atomBits)
    (hs : ∀ point, HeightBound (spike.get point).decode spikeBits) (point : Fin charts) :
    HeightBound (targetEntry feature allowed line atom spike point).data.decode
      (targetHeight charts colors features atomBits spikeBits) := by
  have hr : HeightBound (1 - atom.decode) (atomBits + 1) := by
    simpa only [sub_eq_add_neg, Nat.zero_add] using HeightBound.one.add ha.neg
  have ho := ha.div hr
  have hd := defect_height feature allowed line spike spikeBits hs point
  have ht := HeightBound.one.add (ho.mul hd).neg
  convert ht using 1
  · simp only [targetEntry, difference_value, RationalBits.multiply_value, quotient_value, one_value,
      sub_eq_add_neg]
  · unfold targetHeight
    omega

theorem targetEntry_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (atom : RationalBits) (spike : Vector RationalBits charts)
    (atomBits spikeBits : ℕ) (ha : HeightBound atom.decode atomBits)
    (hs : ∀ point, HeightBound (spike.get point).decode spikeBits) (point : Fin charts) :
    (targetEntry feature allowed line atom spike point).work ≤ targetWork charts colors features atomBits spikeBits := by
  let H := targetHeight charts colors features atomBits spikeBits
  have haH : HeightBound atom.decode H := ha.mono (by dsimp [H, targetHeight]; omega)
  have hone : HeightBound one.decode H := by rw [one_value]; exact HeightBound.one.mono (Nat.zero_le _)
  have hr : HeightBound (difference one atom).data.decode H := by
    rw [difference_value, one_value]
    have hh := HeightBound.one.add ha.neg
    rw [← sub_eq_add_neg] at hh
    exact hh.mono (by dsimp [H, targetHeight]; omega)
  have ho : HeightBound (quotient atom (difference one atom).data).data.decode H := by
    rw [quotient_value, difference_value, one_value]
    have hh := ha.div (show HeightBound (1 - atom.decode) (atomBits + 1) by
      simpa only [sub_eq_add_neg, Nat.zero_add] using HeightBound.one.add ha.neg)
    exact hh.mono (by dsimp [H, targetHeight]; omega)
  have hd := defect_height feature allowed line spike spikeBits hs point
  have hdH := hd.mono (show defectHeight charts colors features spikeBits ≤ H by dsimp [H, targetHeight]; omega)
  have hp : HeightBound (multiply (quotient atom (difference one atom).data).data
      (defect feature allowed line spike point).data).data.decode H := by
    rw [RationalBits.multiply_value, quotient_value, difference_value, one_value]
    have hh := (ha.div (show HeightBound (1 - atom.decode) (atomBits + 1) by
      simpa only [sub_eq_add_neg, Nat.zero_add] using HeightBound.one.add ha.neg)).mul hd
    exact hh.mono (by dsimp [H, targetHeight]; omega)
  have wr := difference_work one atom H hone haH
  have wo := quotient_work atom (difference one atom).data H haH hr
  have wd := defect_work feature allowed line spike spikeBits hs point
  have wp := RationalBits.multiply_work (quotient atom (difference one atom).data).data
    (defect feature allowed line spike point).data H ho hdH
  have wt := difference_work one
    (multiply (quotient atom (difference one atom).data).data (defect feature allowed line spike point).data).data H hone hp
  simp only [targetEntry, targetWork]
  change _ ≤ offLineWork charts colors features spikeBits + 7 * primitiveWorkBound H + 11
  omega

theorem maskedEntry_work {charts : ℕ} (safe : Vector Bool charts) (profile : Vector RationalBits charts)
    (point : Fin charts) : (maskedEntry safe profile point).work ≤ 6 * charts + 8 := by
  have hs := readVector_work false safe point
  have hp := readVector_work zero profile point
  simp only [maskedEntry]
  split <;> dsimp only <;> omega

def storedHeight (charts colors features atomBits : ℕ) : ℕ :=
  chartProjectionHeight charts colors features 0 + targetHeight charts colors features atomBits (2 * charts)

def iterateHeight (charts colors features atomBits steps : ℕ) : ℕ :=
  steps * ((3 * (charts ^ 2 + charts) + 1) * storedHeight charts colors features atomBits + charts + 1)

def regularWork (charts colors features atomBits steps : ℕ) : ℕ :=
  (charts * (spikeWork charts + 2) + 2) + deletionMatrixWork charts colors features +
    (charts * (targetWork charts colors features atomBits (2 * charts) + 2) + 2) +
    (steps * iterationWorkStep charts (storedHeight charts colors features atomBits) steps + 2 * charts + 2) +
    (charts * (6 * charts + 10) + 2) + 5

theorem regular_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (safe fiber : Vector Bool charts) (atom : RationalBits)
    (atomBits steps : ℕ) (ha : HeightBound atom.decode atomBits) :
    (regular feature allowed line safe fiber atom steps).work ≤ regularWork charts colors features atomBits steps := by
  let spike := buildArray charts (chartSpike fiber)
  let matrix := chartDeletionMatrix feature allowed safe
  let rhs := buildArray charts (targetEntry feature allowed line atom spike.data)
  let raw := iteration matrix.data rhs.data steps
  let H := storedHeight charts colors features atomBits
  have hs (point : Fin charts) : HeightBound (spike.data.get point).decode (2 * charts) := by
    dsimp [spike]
    rw [buildArray_get, chartSpike_value]
    exact chartSpikeProgram_height charts _ point
  have hm (output input : Fin charts) : HeightBound ((matrix.data.get output).get input).decode H := by
    dsimp [matrix]
    rw [chartDeletionMatrix_value]
    exact (chartDeletionMatrixProgram_height charts colors features _ _ _ output input).mono
      (by dsimp [H, storedHeight]; omega)
  have hr (point : Fin charts) : HeightBound (rhs.data.get point).decode H := by
    dsimp [rhs]
    rw [buildArray_get]
    exact (targetEntry_height feature allowed line atom spike.data atomBits (2 * charts) ha hs point).mono
      (by dsimp [H, storedHeight]; omega)
  have ws := buildArray_work charts (spikeWork charts) _ (chartSpike_work fiber)
  have wm := chartDeletionMatrix_work feature allowed safe
  have wr := buildArray_work charts (targetWork charts colors features atomBits (2 * charts)) _
    (targetEntry_work feature allowed line atom spike.data atomBits (2 * charts) ha hs)
  have wi := iteration_work matrix.data rhs.data H steps steps hm hr le_rfl
  have wo := buildArray_work charts (6 * charts + 8) _ (maskedEntry_work safe raw.data)
  change spike.work ≤ charts * (spikeWork charts + 2) + 2 at ws
  change matrix.work ≤ deletionMatrixWork charts colors features at wm
  change rhs.work ≤ charts * (targetWork charts colors features atomBits (2 * charts) + 2) + 2 at wr
  change raw.work ≤ steps * iterationWorkStep charts (storedHeight charts colors features atomBits) steps + 2 * charts + 2 at wi
  have hcost : 6 * charts + 8 + 2 = 6 * charts + 10 := by omega
  rw [hcost] at wo
  change spike.work + matrix.work + rhs.work + raw.work +
    (buildArray charts (maskedEntry safe raw.data)).work + 5 ≤ _
  unfold regularWork
  omega

theorem regular_height {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (safe fiber : Vector Bool charts) (atom : RationalBits)
    (atomBits steps : ℕ) (ha : HeightBound atom.decode atomBits) (point : Fin charts) :
    HeightBound ((regular feature allowed line safe fiber atom steps).data.get point).decode
      (iterateHeight charts colors features atomBits steps) := by
  let spike := buildArray charts (chartSpike fiber)
  let matrix := chartDeletionMatrix feature allowed safe
  let rhs := buildArray charts (targetEntry feature allowed line atom spike.data)
  let H := storedHeight charts colors features atomBits
  have hs (input : Fin charts) : HeightBound (spike.data.get input).decode (2 * charts) := by
    dsimp [spike]
    rw [buildArray_get, chartSpike_value]
    exact chartSpikeProgram_height charts _ input
  have hm (output input : Fin charts) : HeightBound ((matrix.data.get output).get input).decode H := by
    dsimp [matrix]
    rw [chartDeletionMatrix_value]
    exact (chartDeletionMatrixProgram_height charts colors features _ _ _ output input).mono
      (by dsimp [H, storedHeight]; omega)
  have hr (input : Fin charts) : HeightBound (rhs.data.get input).decode H := by
    dsimp [rhs]
    rw [buildArray_get]
    exact (targetEntry_height feature allowed line atom spike.data atomBits (2 * charts) ha hs input).mono
      (by dsimp [H, storedHeight]; omega)
  have hi : HeightBound ((iteration matrix.data rhs.data steps).data.get point).decode
      (iterateHeight charts colors features atomBits steps) := by
    rw [iteration_value]
    simpa only [iterateHeight, H, Fintype.card_fin] using
      linearIteration_height (fun output input => ((matrix.data.get output).get input).decode)
        (fun input => (rhs.data.get input).decode) H steps hm hr point
  have ho : HeightBound (maskedEntry safe (iteration matrix.data rhs.data steps).data point).data.decode
      (iterateHeight charts colors features atomBits steps) := by
    rw [maskedEntry_value]
    split
    · exact hi
    · exact HeightBound.zero.mono (Nat.zero_le _)
  simpa only [regular, buildArray_get] using ho

end CurrentAFT.CurrentFlagBinary

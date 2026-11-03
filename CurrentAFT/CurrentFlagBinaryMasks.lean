import CurrentAFT.CurrentFlagBinaryCost
import AFT.BinaryChartSupports
import AFT.BinaryChartCoordinates
import AFT.BinaryDataArrays

/-!
# Explicit masks for the current marked chart fiber

The public marked chart fixes its base and sets its shear to zero.  Only
nonzero-first-coordinate protected inputs constrain its scale.  These are
actual sequential Boolean tests, with no support-membership oracle.
-/

namespace CurrentAFT.CurrentFlagBinaryMasks

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 400000

def onLine (cutoff : ℕ) (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) : CountedValue Bool :=
  let doubled := doubleCounter cutoff
  let source := divideCounter index.val doubled.count.succ
  let result := equalCounter source.quotient cutoff
  ⟨result.value, doubled.work + source.work + result.work + 3⟩

theorem onLine_value (cutoff : ℕ) (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) :
    (onLine cutoff index).value = true ↔ ((finiteInputEquiv cutoff index).1 : ℤ) = 0 := by
  simp only [onLine, equalCounter_value, doubleCounter_value, Nat.succ_eq_add_one,
    (divideCounter_value index.val (2 * cutoff + 1) (by omega)).1]
  simp only [finiteInputEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, finProdFinEquiv_symm_apply,
    FiniteConvolutionProgram.windowIndexEquiv, Equiv.coe_fn_mk, Prod.map_apply]
  change index.val / (2 * cutoff + 1) = cutoff ↔
    ((index.val / (2 * cutoff + 1) : ℕ) : ℤ) - cutoff = 0
  omega

def onLineWork (cutoff : ℕ) : ℕ :=
  let count := (2 * cutoff + 1) * (2 * cutoff + 1)
  3 * cutoff + 1 + 500 * (count + (2 * cutoff + 1) + 2) ^ 2 + 3 * (count + cutoff) + 5

theorem onLine_work (cutoff : ℕ) (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) :
    (onLine cutoff index).work ≤ onLineWork cutoff := by
  have hd := divideCounter_work index.val (2 * cutoff + 1) (by omega)
  have hd' : (divideCounter index.val (2 * cutoff + 1)).work ≤
      500 * (((2 * cutoff + 1) * (2 * cutoff + 1)) + (2 * cutoff + 1) + 2) ^ 2 := by
    apply hd.trans
    gcongr
    exact index.isLt.le
  have he := equalCounter_work (divideCounter index.val (2 * cutoff + 1)).quotient cutoff
  rw [(divideCounter_value index.val (2 * cutoff + 1) (by omega)).1] at he
  have hq := (Nat.div_le_self index.val (2 * cutoff + 1)).trans index.isLt.le
  simp only [onLine, doubleCounter_value, Nat.succ_eq_add_one, doubleCounter_work, onLineWork,
    (divideCounter_value index.val (2 * cutoff + 1) (by omega)).1]
  omega

def offLineAllowed {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (point : Fin charts) (index : Fin features) : CountedValue Bool :=
  let active := readVector false line index
  let permitted := chartAllowedAt feature allowed point index
  ⟨active.value || permitted.value, active.work + permitted.work + 2⟩

theorem offLineAllowed_value {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (point : Fin charts) (index : Fin features) :
    (offLineAllowed feature allowed line point index).value = true ↔
      line.get index ≠ true → (allowed.get index).get ((feature.get index).get point) = true := by
  simp only [offLineAllowed, readVector_value, chartAllowedAt_value, Bool.or_eq_true, or_iff_not_imp_left]

def fiberAt {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (base scale shear : Vector (Fin colors) charts)
    (mark : Fin colors) (point : Fin charts) : CountedValue Bool :=
  let permitted := countedFinAll features (offLineAllowed feature allowed line point)
  let b := readVector 0 base point
  let s := readVector 0 scale point
  let h := readVector 0 shear point
  let isMark := equalCounter b.value.val mark.val
  let isZeroScale := equalCounter s.value.val 0
  let isZeroShear := equalCounter h.value.val 0
  ⟨isMark.value && !isZeroScale.value && isZeroShear.value && permitted.value,
    permitted.work + b.work + s.work + h.work + isMark.work + isZeroScale.work + isZeroShear.work + 7⟩

theorem fiberAt_value {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (base scale shear : Vector (Fin colors) charts)
    (mark : Fin colors) (point : Fin charts) :
    (fiberAt feature allowed line base scale shear mark point).value = true ↔
      base.get point = mark ∧ scale.get point ≠ 0 ∧ shear.get point = 0 ∧
        ∀ index, line.get index ≠ true → (allowed.get index).get ((feature.get index).get point) = true := by
  simp only [fiberAt, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, readVector_value,
    equalCounter_value, countedFinAll_value, offLineAllowed_value, and_assoc]
  have hscale : (scale.get point).val = 0 ↔ scale.get point = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have hshear : (shear.get point).val = 0 ↔ shear.get point = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have hn : (equalCounter (scale.get point).val 0).value ≠ true ↔ scale.get point ≠ 0 :=
    not_congr ((equalCounter_value _ _).trans hscale)
  simp only [Fin.val_inj, hn, hshear]

def fiberWork (charts colors features : ℕ) : ℕ :=
  features * (9 * features + 4 * charts + 4 * colors + 23) +
    9 * charts + 12 * colors + 25

theorem fiberAt_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (base scale shear : Vector (Fin colors) charts)
    (mark : Fin colors) (point : Fin charts) :
    (fiberAt feature allowed line base scale shear mark point).work ≤ fiberWork charts colors features := by
  have hw (index : Fin features) : (offLineAllowed feature allowed line point index).work ≤
      9 * features + 4 * charts + 4 * colors + 21 := by
    have hl := readVector_work false line index
    have ha := chartAllowedAt_work feature allowed point index
    simp only [offLineAllowed]
    omega
  have hall := countedFinAll_work features (offLineAllowed feature allowed line point)
    (9 * features + 4 * charts + 4 * colors + 21) hw
  have hb := readVector_work (0 : Fin colors) base point
  have hs := readVector_work (0 : Fin colors) scale point
  have hh := readVector_work (0 : Fin colors) shear point
  have hm := equalCounter_work (readVector (0 : Fin colors) base point).value.val mark.val
  have hz := equalCounter_work (readVector (0 : Fin colors) scale point).value.val 0
  have ht := equalCounter_work (readVector (0 : Fin colors) shear point).value.val 0
  have hbm := (readVector (0 : Fin colors) base point).value.isLt
  have hsm := (readVector (0 : Fin colors) scale point).value.isLt
  have hhm := (readVector (0 : Fin colors) shear point).value.isLt
  have hmark := mark.isLt
  simp only [fiberAt, fiberWork]
  nlinarith

end CurrentAFT.CurrentFlagBinaryMasks

import CurrentAFT.CurrentFlagBinaryMasks
import AFT.BinaryProtectedMetadataCost
import AFT.BinaryProtectedMetadataSemantics

/-!
# Generating the current flag arrays from public integer data

The inherited feature, palette, and safe tables are reused.  Their old
single-point fiber is discarded.  A fresh fiber fixes base and shear and
uses the complete zero-first-coordinate line mask.
-/

namespace CurrentAFT.CurrentFlagBinaryMetadata

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits CurrentFlagBinaryMasks
open scoped BigOperators
set_option maxHeartbeats 400000

structure Data (charts colors features : ℕ) where
  feature : Vector (Vector (Fin colors) charts) features
  allowed : Vector (Vector Bool colors) features
  safe : Vector Bool charts
  line : Vector Bool features
  fiber : Vector Bool charts

def coordinates (modulus : ℕ) [NeZero modulus]
    (point : Fin (modulus * (modulus * modulus))) : CountedValue (Fin modulus × Fin modulus × Fin modulus) :=
  let result := binaryChartCoordinates modulus point.val
  let bounds := binaryChartCoordinates_bounds modulus point.val (NeZero.pos _) point.isLt
  ⟨(⟨result.offset, bounds.1⟩, ⟨result.scale, bounds.2.1⟩, ⟨result.shear, bounds.2.2⟩), result.work + 3⟩

theorem finEquiv_cast (modulus : ℕ) [NeZero modulus] (value : Fin modulus) :
    (ZMod.finEquiv modulus) value = (value.val : ZMod modulus) := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => apply Fin.ext; exact (Nat.mod_eq_of_lt value.isLt).symm

theorem coordinates_field (modulus : ℕ) [NeZero modulus]
    (point : Fin (modulus * (modulus * modulus))) :
    ((ZMod.finEquiv modulus) (coordinates modulus point).value.1,
      (ZMod.finEquiv modulus) (coordinates modulus point).value.2.1,
      (ZMod.finEquiv modulus) (coordinates modulus point).value.2.2) = finiteChartEquiv modulus point := by
  simp only [coordinates, finEquiv_cast]
  exact binaryChartCoordinates_semantics modulus point

def build (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
    CountedValue (Data (modulus * (modulus * modulus)) modulus ((2 * cutoff + 1) * (2 * cutoff + 1))) :=
  let inherited := protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark
  let line := storeData ((2 * cutoff + 1) * (2 * cutoff + 1)) (onLine cutoff)
  let base := storeData (modulus * (modulus * modulus)) (fun point =>
    let result := coordinates modulus point
    ⟨result.value.1, result.work + 1⟩)
  let shear := storeData (modulus * (modulus * modulus)) (fun point =>
    let result := coordinates modulus point
    ⟨result.value.2.2, result.work + 1⟩)
  let fiber := storeData (modulus * (modulus * modulus))
    (fiberAt inherited.value.feature inherited.value.allowed line.value base.value inherited.value.scale shear.value mark)
  ⟨⟨inherited.value.feature, inherited.value.allowed, inherited.value.safe, line.value, fiber.value⟩,
    inherited.work + line.work + base.work + shear.work + fiber.work + 5⟩

theorem build_feature (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
    (fun index point => (((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.feature).get index).get point) =
      finiteProtectedFeatures cutoff modulus := by
  exact protectedMetadata_feature cutoff modulus boundarySign baselineSign boundary baseline mark

theorem build_allowed (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
    (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) (color : Fin modulus) :
    (((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.allowed).get index).get color = true ↔
      color ∈ finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) index := by
  exact protectedMetadata_allowed cutoff modulus boundarySign baselineSign boundary baseline mark index color

theorem build_safe (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
    (point : Fin (modulus * (modulus * modulus))) :
    ((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.safe).get point = true ↔
      point ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
        (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline)) := by
  exact protectedMetadata_safe cutoff modulus boundarySign baselineSign boundary baseline mark point

theorem build_line (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
    (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) :
    ((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.line).get index = true ↔
      ((finiteInputEquiv cutoff index).1 : ℤ) = 0 := by
  simp only [build, storeData_get]
  exact onLine_value cutoff index

theorem build_fiber (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
    (point : Fin (modulus * (modulus * modulus))) :
    ((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.fiber).get point = true ↔
      (coordinates modulus point).value.1 = mark ∧ finiteAffineScale modulus point ≠ 0 ∧
        (coordinates modulus point).value.2.2 = 0 ∧
        ∀ index, ((finiteInputEquiv cutoff index).1 : ℤ) ≠ 0 →
          finiteProtectedFeatures cutoff modulus index point ∈
            finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) index := by
  simp only [build, storeData_get, fiberAt_value]
  rw [protectedMetadata_scale]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  apply forall_congr'
  intro index
  apply imp_congr (not_congr (onLine_value cutoff index))
  have hf := congrFun (congrFun (protectedMetadata_feature cutoff modulus boundarySign baselineSign boundary baseline mark) index) point
  rw [hf]
  exact protectedMetadata_allowed cutoff modulus boundarySign baselineSign boundary baseline mark index _

def workBound (cutoff modulus boundaryBits baselineBits : ℕ) : ℕ :=
  let charts := modulus * (modulus * modulus)
  let features := (2 * cutoff + 1) * (2 * cutoff + 1)
  protectedMetadataWork cutoff modulus boundaryBits baselineBits +
    (features * (onLineWork cutoff + 2) + 2) +
    2 * (charts * (protectedScaleWork modulus charts + 6) + 2) +
    (charts * (fiberWork charts modulus features + 2) + 2) + 5

theorem build_work (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
    (build cutoff modulus boundarySign baselineSign boundary baseline mark).work ≤
      workBound cutoff modulus boundary.length baseline.length := by
  let charts := modulus * (modulus * modulus)
  let features := (2 * cutoff + 1) * (2 * cutoff + 1)
  let inherited := protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark
  let line := storeData features (onLine cutoff)
  let base := storeData charts (fun point =>
    let result := coordinates modulus point
    (⟨result.value.1, result.work + 1⟩ : CountedValue (Fin modulus)))
  let shear := storeData charts (fun point =>
    let result := coordinates modulus point
    (⟨result.value.2.2, result.work + 1⟩ : CountedValue (Fin modulus)))
  let fiber := storeData charts
    (fiberAt inherited.value.feature inherited.value.allowed line.value base.value inherited.value.scale shear.value mark)
  have hi := protectedMetadata_work cutoff modulus boundarySign baselineSign boundary baseline mark
  have hl := storeData_work features (onLineWork cutoff) (onLine cutoff) (onLine_work cutoff)
  have hc (point : Fin charts) : (coordinates modulus point).work + 1 ≤ protectedScaleWork modulus charts + 4 := by
    have hw := (binaryChartCoordinates_work modulus point.val (NeZero.pos _)).trans
      (protectedScaleWork_mono le_rfl point.isLt.le)
    change (binaryChartCoordinates modulus point.val).work + 3 + 1 ≤ _
    omega
  have hb := storeData_work charts (protectedScaleWork modulus charts + 4)
    (fun point => let result := coordinates modulus point
      (⟨result.value.1, result.work + 1⟩ : CountedValue (Fin modulus))) hc
  have hh := storeData_work charts (protectedScaleWork modulus charts + 4)
    (fun point => let result := coordinates modulus point
      (⟨result.value.2.2, result.work + 1⟩ : CountedValue (Fin modulus))) hc
  have hf := storeData_work charts (fiberWork charts modulus features) _
    (fiberAt_work inherited.value.feature inherited.value.allowed line.value base.value inherited.value.scale shear.value mark)
  change inherited.work ≤ _ at hi
  change line.work ≤ _ at hl
  change base.work ≤ _ at hb
  change shear.work ≤ _ at hh
  change fiber.work ≤ charts * (fiberWork charts modulus features + 2) + 2 at hf
  simp only [Nat.add_assoc] at hb hh
  norm_num only at hb hh
  change inherited.work + line.work + base.work + shear.work + fiber.work + 5 ≤
    protectedMetadataWork cutoff modulus boundary.length baseline.length +
      (features * (onLineWork cutoff + 2) + 2) +
      2 * (charts * (protectedScaleWork modulus charts + 6) + 2) +
      (charts * (fiberWork charts modulus features + 2) + 2) + 5
  omega

end CurrentAFT.CurrentFlagBinaryMetadata

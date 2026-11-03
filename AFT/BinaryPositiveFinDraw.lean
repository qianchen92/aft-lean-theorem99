import AFT.BinaryPositiveDraw
import AFT.MarkedChartFinSampler
import AFT.RationalPaletteSampler

/-! Positive sampling on any nonempty stored array. -/
namespace AFT.BinaryArithmetic
open RationalNumerics RationalBits BoundaryCalibration BetaReference

def binaryPositiveFinDraw {count : ℕ} [NeZero count] (raw : Vector RationalBits count)
    (bits : ℕ) (word : Fin (bits+count+1) → Fin 2) : CountedNatural := by
  cases count with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ pred => exact binaryPositiveDraw raw bits word

theorem binaryPositiveFinDraw_lt {count : ℕ} [NeZero count] (raw : Vector RationalBits count)
    (bits : ℕ) (word : Fin (bits+count+1) → Fin 2) :
    (binaryPositiveFinDraw raw bits word).value < count := by
  cases count with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ pred =>
    change (binaryPositiveDraw raw bits word).value < _
    rw [binaryPositiveDraw_value]
    exact Fin.isLt _

theorem binaryPositiveFinDraw_work {count : ℕ} [NeZero count] (raw : Vector RationalBits count)
    (height bits : ℕ) (hh : ∀ index, HeightBound (raw.get index).decode height)
    (word : Fin (bits+count+1) → Fin 2) :
    (binaryPositiveFinDraw raw bits word).work ≤ binaryPositiveDrawWork count height bits := by
  cases count with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ pred => exact binaryPositiveDraw_work raw height bits hh word

theorem binaryPositiveFinDraw_marked_value (charts colors features : ℕ) [NeZero charts]
    (raw : Vector RationalBits charts)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe fiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ) (steps bits : ℕ)
    (hv : ∀ index, (raw.get index).decode=(markedChartWeightProgram charts colors features feature allowed safe fiber marked atom steps).get index)
    (word : Fin (bits+charts+1) → Fin 2) :
    (binaryPositiveFinDraw raw bits word).value=
      (markedChartFinDraw charts colors features feature allowed safe fiber marked atom steps bits word).val := by
  cases charts with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ pred =>
    change (binaryPositiveDraw raw bits word).value=_
    rw [binaryPositiveDraw_value]
    simp only [markedChartFinDraw,markedChartDraw]
    congr 2
    exact funext hv

theorem binaryPositiveFinDraw_palette_value {count : ℕ} [NeZero count] (raw : Vector RationalBits count)
    (bits : ℕ) (word : Fin (bits+count+1) → Fin 2) :
    (binaryPositiveFinDraw raw bits word).value=
      (RationalPaletteSampler.draw count (NeZero.pos _) (fun index => (raw.get index).decode) bits word).val := by
  cases count with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ pred => exact binaryPositiveDraw_value raw bits word

end AFT.BinaryArithmetic

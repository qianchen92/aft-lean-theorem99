import CurrentAFT.CurrentFlagWeightArray
import AFT.BinaryPositiveFinDraw
import AFT.BinaryLegalChart

/-! Positive finite-bit array sampling with an actual safe-mask fallback scan. -/

namespace CurrentAFT.CurrentFlagDraw

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000

def draw {charts : ℕ} [NeZero charts] (raw : Vector RationalBits charts) (mask : Vector Bool charts)
    (bits : ℕ) (word : Fin (bits + charts + 1) → Fin 2) : CountedValue (Fin charts) :=
  let selected := binaryPositiveFinDraw raw bits word
  let point : Fin charts := ⟨selected.value, binaryPositiveFinDraw_lt raw bits word⟩
  let legal := binaryLegalChartIndex mask point
  ⟨legal.value, selected.work + legal.work + 2⟩

theorem draw_value {charts : ℕ} [NeZero charts] (raw : Vector RationalBits charts) (mask : Vector Bool charts)
    (bits : ℕ) (word : Fin (bits + charts + 1) → Fin 2) :
    (draw raw mask bits word).value = legalChartIndex charts (maskSet mask)
      (RationalPaletteSampler.draw charts (NeZero.pos _) (fun point => (raw.get point).decode) bits word) := by
  have hp : (⟨(binaryPositiveFinDraw raw bits word).value, binaryPositiveFinDraw_lt raw bits word⟩ : Fin charts) =
      RationalPaletteSampler.draw charts (NeZero.pos _) (fun point => (raw.get point).decode) bits word := by
    apply Fin.ext
    exact binaryPositiveFinDraw_palette_value raw bits word
  unfold draw
  dsimp only
  rw [binaryLegalChartIndex_value _ _ (maskSet mask) (fun _ => by
    simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]), hp]

def workBound (charts height bits : ℕ) : ℕ :=
  binaryPositiveDrawWork charts height bits + 7 * charts + 13

theorem draw_work {charts : ℕ} [NeZero charts] (raw : Vector RationalBits charts) (mask : Vector Bool charts)
    (height bits : ℕ) (hh : ∀ point, HeightBound (raw.get point).decode height)
    (word : Fin (bits + charts + 1) → Fin 2) :
    (draw raw mask bits word).work ≤ workBound charts height bits := by
  have hp := binaryPositiveFinDraw_work raw height bits hh word
  have hl := binaryLegalChartIndex_work mask
    (⟨(binaryPositiveFinDraw raw bits word).value, binaryPositiveFinDraw_lt raw bits word⟩ : Fin charts)
  simp only [draw, workBound]
  omega

noncomputable section
open scoped Classical

theorem draw_supported {charts : ℕ} [NeZero charts] (raw : Vector RationalBits charts) (mask : Vector Bool charts)
    (reference : FiniteDist (Fin charts))
    (hsupport : ∀ point, point ∉ maskSet mask → reference.weight point = 0)
    (bits : ℕ) (word : Fin (bits + charts + 1) → Fin 2) :
    (draw raw mask bits word).value ∈ maskSet mask := by
  rw [draw_value]
  exact legalChartIndex_mem charts _ (supported_set_nonempty reference _ hsupport) _

theorem draw_l1 {charts : ℕ} [NeZero charts] (raw : Vector RationalBits charts) (mask : Vector Bool charts)
    (reference : FiniteDist (Fin charts))
    (hsupport : ∀ point, point ∉ maskSet mask → reference.weight point = 0)
    (error : ℝ) (herror : (∑ point, |((raw.get point).decode : ℝ) - reference.weight point|) ≤ error)
    (hsmall : error ≤ 1 / 2) (bits : ℕ) :
    (∑ point, |((FiniteDist.uniform (Fin (bits + charts + 1) → Fin 2)).map
      (fun word => (draw raw mask bits word).value)).weight point - reference.weight point|) ≤
      1 / (2 : ℝ) ^ bits + 4 * error := by
  have hp := RationalPaletteSampler.draw_l1 charts (NeZero.pos _) (fun point => (raw.get point).decode)
    bits reference error herror hsmall
  have hl := legalChartIndex_l1 charts (maskSet mask)
    ((FiniteDist.uniform (Fin (bits + charts + 1) → Fin 2)).map
      (RationalPaletteSampler.draw charts (NeZero.pos _) (fun point => (raw.get point).decode) bits))
    reference hsupport
  rw [FiniteDist.map_map] at hl
  simpa only [Function.comp_def, draw_value] using hl.trans hp

end
end CurrentAFT.CurrentFlagDraw

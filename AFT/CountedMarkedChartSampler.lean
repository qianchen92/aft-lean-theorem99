import AFT.CountedChartProgram
import AFT.CountedPositiveSampling
import AFT.MarkedChartFinSampler

/-! # The chart matrix program and fair-bit ticket sampler are one executable -/
namespace AFT.BoundaryCalibration
open RationalNumerics BetaReference
open scoped BigOperators

 def countedMarkedChartDraw (chartPred colors features : ℕ)
    (feature : Fin features → Fin (chartPred+1) → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin (chartPred+1))) (marked : Fin features) (atom : ℚ)
    (steps bits : ℕ) (word : Fin (bits+(chartPred+1)+1) → Fin 2) : CountedNatural :=
  let raw := countedMarkedChartWeightProgram (chartPred+1) colors features feature allowed safe survivingFiber marked atom steps
  let sample := countedPositiveDraw raw.value bits word
  ⟨sample.value,raw.work+sample.work⟩

 theorem countedMarkedChartDraw_value (chartPred colors features : ℕ)
    (feature : Fin features → Fin (chartPred+1) → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin (chartPred+1))) (marked : Fin features) (atom : ℚ)
    (steps bits : ℕ) (word : Fin (bits+(chartPred+1)+1) → Fin 2) :
    (countedMarkedChartDraw chartPred colors features feature allowed safe survivingFiber marked atom steps bits word).value=
      (markedChartDraw chartPred colors features feature allowed safe survivingFiber marked atom steps bits word).val := by
  simp only [countedMarkedChartDraw,countedPositiveDraw_value,countedMarkedChartWeightProgram_value,markedChartDraw]

 theorem countedMarkedChartDraw_work (chartPred colors features : ℕ)
    (feature : Fin features → Fin (chartPred+1) → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin (chartPred+1))) (marked : Fin features) (atom : ℚ)
    (steps bits : ℕ) (word : Fin (bits+(chartPred+1)+1) → Fin 2) :
    (countedMarkedChartDraw chartPred colors features feature allowed safe survivingFiber marked atom steps bits word).work≤
      chartArithmeticWork (chartPred+1) colors features steps+3*bits+14*(chartPred+1)+5 := by
  have hw := countedMarkedChartWeightProgram_work (chartPred+1) colors features feature allowed safe survivingFiber marked atom steps
  have hs := countedPositiveDraw_work
    (countedMarkedChartWeightProgram (chartPred+1) colors features feature allowed safe survivingFiber marked atom steps).value bits word
  simp only [countedMarkedChartDraw]
  omega

 def countedMarkedChartFinDraw (charts colors features : ℕ) [NeZero charts]
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ)
    (steps bits : ℕ) (word : Fin (bits+charts+1) → Fin 2) : CountedNatural := by
  cases charts with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ chartPred => exact countedMarkedChartDraw chartPred colors features feature allowed safe survivingFiber marked atom steps bits word

 theorem countedMarkedChartFinDraw_value (charts colors features : ℕ) [NeZero charts]
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ)
    (steps bits : ℕ) (word : Fin (bits+charts+1) → Fin 2) :
    (countedMarkedChartFinDraw charts colors features feature allowed safe survivingFiber marked atom steps bits word).value=
      (markedChartFinDraw charts colors features feature allowed safe survivingFiber marked atom steps bits word).val := by
  cases charts with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ chartPred => exact countedMarkedChartDraw_value chartPred colors features feature allowed safe survivingFiber marked atom steps bits word

 theorem countedMarkedChartFinDraw_work (charts colors features : ℕ) [NeZero charts]
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ)
    (steps bits : ℕ) (word : Fin (bits+charts+1) → Fin 2) :
    (countedMarkedChartFinDraw charts colors features feature allowed safe survivingFiber marked atom steps bits word).work≤
      chartArithmeticWork charts colors features steps+3*bits+14*charts+5 := by
  cases charts with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ chartPred => exact countedMarkedChartDraw_work chartPred colors features feature allowed safe survivingFiber marked atom steps bits word

end AFT.BoundaryCalibration

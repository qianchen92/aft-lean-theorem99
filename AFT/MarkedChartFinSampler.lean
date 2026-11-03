import AFT.MarkedChartSampler

/-! # The finite sampler on any positive chart array size -/
namespace AFT.BoundaryCalibration
open scoped BigOperators

def markedChartFinDraw (charts colors features : ℕ) [NeZero charts]
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ)
    (steps bits : ℕ) (word : Fin (bits+charts+1) → Fin 2) : Fin charts := by
  cases charts with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ chartPred => exact markedChartDraw chartPred colors features feature allowed safe survivingFiber marked atom steps bits word

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

 theorem markedChartFinDraw_l1
    (charts colors features : ℕ) [NeZero charts]
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ)
    (ha : 0≤(atom : ℝ)) (ha1 : (atom : ℝ)≤1)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖<1)
    (hquarter : ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖≤1/4)
    (hdefect : ‖spikeDefect (FiniteDist.uniform (Fin charts)) feature allowed marked (atom : ℝ)
      (restrictedDensity (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber))‖≤1/25)
    (reference : FiniteDist (Fin charts))
    (href : ∀ point, reference.weight point=
      explicitMarkedChartDensity charts colors features feature allowed safe survivingFiber marked atom hD point/charts)
    (steps bits : ℕ) (hsteps : 1≤steps) :
    (∑point,|((FiniteDist.independent (fun _ : Fin (bits+charts+1) => FiniteDist.uniform (Fin 2))).map
      (markedChartFinDraw charts colors features feature allowed safe survivingFiber marked atom steps bits)).weight point-
      reference.weight point|)≤8*(1/4 : ℝ)^steps+1/(2 : ℝ)^bits := by
  cases charts with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ chartPred =>
    simpa only [markedChartFinDraw] using markedChartDraw_l1 chartPred colors features feature allowed safe survivingFiber marked atom
      ha ha1 hD hquarter hdefect reference (by simpa only [Nat.cast_add,Nat.cast_one] using href) steps bits hsteps

end
end AFT.BoundaryCalibration

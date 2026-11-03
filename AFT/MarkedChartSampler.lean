import AFT.MarkedChartProgram

/-! # Executable finite fair-bit sampler for the marked chart -/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators

def markedChartDraw (chartPred colors features : ℕ)
    (feature : Fin features → Fin (chartPred+1) → Fin colors)
    (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin (chartPred+1))) (marked : Fin features) (atom : ℚ)
    (steps bits : ℕ) (word : Fin (bits+(chartPred+1)+1) → Fin 2) : Fin (chartPred+1) :=
  positiveNormalizeDraw (fun point =>
    (markedChartWeightProgram (chartPred+1) colors features feature allowed safe survivingFiber marked atom steps).get point) bits word

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 theorem markedChartWeightProgram_l1
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
    (steps : ℕ) :
    (∑point,|((markedChartWeightProgram charts colors features feature allowed safe survivingFiber marked atom steps).get point : ℝ)-
      reference.weight point|)≤2*(1/4 : ℝ)^steps := by
  have hq : (0 : ℝ)<charts := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne charts))
  calc
    _ ≤ ∑ _point : Fin charts, (2*(1/4 : ℝ)^steps)/(charts : ℝ) := by
      apply Finset.sum_le_sum
      intro point _
      rw [href point]
      simp only [markedChartWeightProgram,Vector.get_ofFn,Rat.cast_div,Rat.cast_natCast,←sub_div,abs_div,abs_of_pos hq]
      exact div_le_div_of_nonneg_right (markedChartDensityProgram_error charts colors features feature allowed safe survivingFiber
        marked atom ha ha1 hD hquarter hdefect steps point) hq.le
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];field_simp

 theorem markedChartDraw_l1
    (chartPred colors features : ℕ)
    (feature : Fin features → Fin (chartPred+1) → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin (chartPred+1))) (marked : Fin features) (atom : ℚ)
    (ha : 0≤(atom : ℝ)) (ha1 : (atom : ℝ)≤1)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform (Fin (chartPred+1))) feature allowed) (fun x => x∈safe)‖<1)
    (hquarter : ‖deletion (chartProjection (FiniteDist.uniform (Fin (chartPred+1))) feature allowed) (fun x => x∈safe)‖≤1/4)
    (hdefect : ‖spikeDefect (FiniteDist.uniform (Fin (chartPred+1))) feature allowed marked (atom : ℝ)
      (restrictedDensity (FiniteDist.uniform (Fin (chartPred+1))) (fun x => x∈survivingFiber))‖≤1/25)
    (reference : FiniteDist (Fin (chartPred+1)))
    (href : ∀ point, reference.weight point=
      explicitMarkedChartDensity (chartPred+1) colors features feature allowed safe survivingFiber marked atom hD point/(chartPred+1))
    (steps bits : ℕ) (hsteps : 1≤steps) :
    (∑point,|((FiniteDist.independent (fun _ : Fin (bits+(chartPred+1)+1) => FiniteDist.uniform (Fin 2))).map
      (markedChartDraw chartPred colors features feature allowed safe survivingFiber marked atom steps bits)).weight point-
      reference.weight point|)≤8*(1/4 : ℝ)^steps+1/(2 : ℝ)^bits := by
  let raw := fun point =>
    (markedChartWeightProgram (chartPred+1) colors features feature allowed safe survivingFiber marked atom steps).get point
  have hraw := markedChartWeightProgram_l1 (chartPred+1) colors features feature allowed safe survivingFiber marked atom
    ha ha1 hD hquarter hdefect reference (by simpa only [Nat.cast_add,Nat.cast_one] using href) steps
  have hsmall : 2*(1/4 : ℝ)^steps≤1/2 := by
    have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ)≤1/4) (by norm_num : (1/4 : ℝ)≤1) hsteps
    norm_num at hp
    linarith
  have hnormalized := positiveProgramLaw_l1 raw reference (2*(1/4 : ℝ)^steps) hraw hsmall
  have hround := positiveNormalizeDraw_l1 raw bits
  calc
    _ ≤ (∑point,|((FiniteDist.independent (fun _ : Fin (bits+(chartPred+1)+1) => FiniteDist.uniform (Fin 2))).map
      (positiveNormalizeDraw raw bits)).weight point-(positiveProgramLaw raw).weight point|)+
      ∑point,|(positiveProgramLaw raw).weight point-reference.weight point| := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro point _
      exact abs_sub_le _ _ _
    _ ≤ 1/(2 : ℝ)^bits+4*(2*(1/4 : ℝ)^steps) := add_le_add hround hnormalized
    _ = _ := by ring

end
end AFT.BoundaryCalibration

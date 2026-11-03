import AFT.ChartNeumannProgram
import AFT.ExplicitChartDensity
import AFT.RationalPositiveNormalize

/-! # Rational marked-chart density from the explicit protected repair -/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators

def chartSpikeProgram (charts : ℕ) (survivingFiber : Finset (Fin charts)) (point : Fin charts) : ℚ :=
  if point∈survivingFiber then (charts : ℚ)/survivingFiber.card else 0

def chartSpikeDefectProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (marked : Fin features) (atom : ℚ) (spike : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  atom*∑ index,if index=marked then 0 else chartFeatureProgram charts colors (feature index) (allowed index) spike point

def markedChartDensityProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ) (steps : ℕ) : Vector ℚ charts :=
  let spike := chartSpikeProgram charts survivingFiber
  let defect := chartSpikeDefectProgram charts colors features feature allowed marked atom spike
  let base := chartNeumannProgram charts colors features feature allowed safe (fun _ => 1) steps
  let repair := chartNeumannProgram charts colors features feature allowed safe defect steps
  Vector.ofFn (fun point =>
    (if point∈safe then (1-atom)*base.get point-repair.get point else 0)+atom*spike point)

def markedChartWeightProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ) (steps : ℕ) : Vector ℚ charts :=
  let density := markedChartDensityProgram charts colors features feature allowed safe survivingFiber marked atom steps
  Vector.ofFn (fun point => density.get point/(charts : ℚ))

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable (charts colors features : ℕ) [NeZero charts]

 theorem chartSpikeProgram_cast (survivingFiber : Finset (Fin charts)) (point : Fin charts) :
    (chartSpikeProgram charts survivingFiber point : ℝ)=
      restrictedDensity (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber) point := by
  have he : eventMass (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber)=
      (survivingFiber.card : ℝ)/(charts : ℝ) := by
    simp only [eventMass,expectation_apply,FiniteDist.uniform,Fintype.card_fin,eventIndicator]
    rw [←Finset.mul_sum]
    have hs : (∑ x : Fin charts, if x∈survivingFiber then (1 : ℝ) else 0) = survivingFiber.card := by
      calc
        _ = ∑ x∈survivingFiber, (if x∈survivingFiber then (1 : ℝ) else 0) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro x _ hx
          exact if_neg hx
        _ = _ := by simp
    calc
      _ = (charts : ℝ)⁻¹*(∑ x : Fin charts, if x∈survivingFiber then (1 : ℝ) else 0) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> rfl
      _ = _ := by rw [hs];ring
  simp only [chartSpikeProgram,apply_ite,Rat.cast_div,Rat.cast_natCast,Rat.cast_zero,restrictedDensity,eventIndicator,he]
  split_ifs
  · rw [one_div_div]
  · simp

 theorem chartSpikeDefectProgram_cast
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (marked : Fin features) (atom : ℚ) (spike : Fin charts → ℚ) (point : Fin charts) :
    (chartSpikeDefectProgram charts colors features feature allowed marked atom spike point : ℝ)=
      spikeDefect (FiniteDist.uniform (Fin charts)) feature allowed marked (atom : ℝ) (fun x => (spike x : ℝ)) point := by
  simp only [chartSpikeDefectProgram,Rat.cast_mul,Rat.cast_sum,apply_ite,Rat.cast_zero,
    chartFeatureProgram_cast,spikeDefect,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> rfl

 def explicitMarkedChartDensity
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℝ)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖<1)
    (point : Fin charts) : ℝ :=
  let P := chartProjection (FiniteDist.uniform (Fin charts)) feature allowed
  let D := deletion P (fun x => x∈safe)
  let spike := restrictedDensity (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber)
  let defect := spikeDefect (FiniteDist.uniform (Fin charts)) feature allowed marked atom spike
  (if point∈safe then (1-atom)*neumannSolve D hD 1 point-neumannSolve D hD defect point else 0)+atom*spike point

 theorem markedChartDensityProgram_error
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ)
    (ha : 0≤(atom : ℝ)) (ha1 : (atom : ℝ)≤1)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖<1)
    (hquarter : ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖≤1/4)
    (hdefect : ‖spikeDefect (FiniteDist.uniform (Fin charts)) feature allowed marked (atom : ℝ)
      (restrictedDensity (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber))‖≤1/25)
    (steps : ℕ) (point : Fin charts) :
    |((markedChartDensityProgram charts colors features feature allowed safe survivingFiber marked atom steps).get point : ℝ)-
      explicitMarkedChartDensity charts colors features feature allowed safe survivingFiber marked atom hD point|≤
      2*(1/4 : ℝ)^steps := by
  let D := deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)
  let spike := restrictedDensity (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber)
  let defect := spikeDefect (FiniteDist.uniform (Fin charts)) feature allowed marked (atom : ℝ) spike
  let dprog := chartSpikeDefectProgram charts colors features feature allowed marked atom (chartSpikeProgram charts survivingFiber)
  have hcast : (fun x => (dprog x : ℝ))=defect := by
    funext x
    simp only [dprog,chartSpikeDefectProgram_cast,chartSpikeProgram_cast,defect,spike]
  have hb := chartNeumannProgram_error charts colors features feature allowed safe hD hquarter (fun _ => 1) steps point
  have hr := chartNeumannProgram_error charts colors features feature allowed safe hD hquarter dprog steps point
  have hone : ‖fun _ : Fin charts => (1 : ℝ)‖=1 := by
    change ‖(1 : Fin charts → ℝ)‖=1
    exact norm_one
  simp only [Rat.cast_one, hone, mul_one] at hb
  rw [hcast] at hr
  have hr' : |((chartNeumannProgram charts colors features feature allowed safe dprog steps).get point : ℝ)-
      neumannSolve D hD defect point|≤(1/4 : ℝ)^steps*(4/75) := by
    calc
      _ ≤ (1/4 : ℝ)^steps*(4/3*‖defect‖) := hr
      _ ≤ (1/4 : ℝ)^steps*(4/3*(1/25)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hdefect (by norm_num)
      _ = _ := by ring
  by_cases hs : point∈safe
  · simp only [markedChartDensityProgram,Vector.get_ofFn,Rat.cast_add,Rat.cast_sub,
      Rat.cast_mul,Rat.cast_one,chartSpikeProgram_cast,explicitMarkedChartDensity,if_pos hs]
    change |((1-(atom : ℝ))*_ -_+(atom : ℝ)*spike point)-((1-(atom : ℝ))*_-_+(atom : ℝ)*spike point)|≤_
    rw [show ∀ a b c d e : ℝ,(a*b-c+e)-(a*d-(neumannSolve D hD defect point)+e)=
      a*(b-d)-(c-neumannSolve D hD defect point) by intros;ring]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg (by linarith : 0≤1-(atom : ℝ))]
    have ht := add_le_add (mul_le_mul_of_nonneg_left hb (by linarith : 0≤1-(atom : ℝ))) hr'
    apply ht.trans
    have hp : 0≤(1/4 : ℝ)^steps := by positivity
    nlinarith
  · simp only [markedChartDensityProgram,Vector.get_ofFn,
      zero_add,Rat.cast_mul,chartSpikeProgram_cast,explicitMarkedChartDensity,if_neg hs,zero_add,sub_self,abs_zero]
    positivity

end
end AFT.BoundaryCalibration

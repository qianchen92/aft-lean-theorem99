import AFT.BoundarySpike
import AFT.CachedLinearIteration
import AFT.LinearIterationHeight

/-! # Rational finite chart projection and a cached Neumann program

All entries of the unrestricted uniform chart projection are rational.
The program stores its deletion matrix and complete iterate vectors.
-/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators

def chartExpectationProgram (charts : ℕ) (value : Fin charts → ℚ) : ℚ :=
  (∑ chart,value chart)/(charts : ℚ)

def chartConditionalProgram (charts colors : ℕ) (feature : Fin charts → Fin colors)
    (value : Fin charts → ℚ) (color : Fin colors) : ℚ :=
  (colors : ℚ)*chartExpectationProgram charts (fun chart => if feature chart=color then value chart else 0)

def chartFeatureProgram (charts colors : ℕ) (feature : Fin charts → Fin colors)
    (allowed : Finset (Fin colors)) (value : Fin charts → ℚ) (chart : Fin charts) : ℚ :=
  if feature chart∈allowed then
    chartConditionalProgram charts colors feature value (feature chart)-
      (∑color∈allowed,chartConditionalProgram charts colors feature value color)/(allowed.card : ℚ)
  else 0

def chartProjectionProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (value : Fin charts → ℚ) (chart : Fin charts) : ℚ :=
  chartExpectationProgram charts value+∑index,chartFeatureProgram charts colors (feature index) (allowed index) value chart

def chartDeletionProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (value : Fin charts → ℚ) (chart : Fin charts) : ℚ :=
  chartProjectionProgram charts colors features feature allowed (fun input => if input∈safe then 0 else value input) chart

def chartDeletionMatrixProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (output input : Fin charts) : ℚ :=
  -chartDeletionProgram charts colors features feature allowed safe (fun point => if point=input then 1 else 0) output

def chartNeumannProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (rhs : Fin charts → ℚ) (steps : ℕ) : Vector ℚ charts :=
  cachedLinearIteration (cachedMatrix charts (chartDeletionMatrixProgram charts colors features feature allowed safe))
    (Vector.ofFn rhs) steps

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (charts colors features : ℕ) [NeZero charts]

 theorem chartExpectationProgram_cast (value : Fin charts → ℚ) :
    (chartExpectationProgram charts value : ℝ)=expectation (FiniteDist.uniform (Fin charts)) (fun x => (value x : ℝ)) := by
  simp only [chartExpectationProgram,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,expectation_apply,
    FiniteDist.uniform,Fintype.card_fin]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

 theorem chartConditionalProgram_cast (feature : Fin charts → Fin colors)
    (value : Fin charts → ℚ) (color : Fin colors) :
    (chartConditionalProgram charts colors feature value color : ℝ)=
      conditional (FiniteDist.uniform (Fin charts)) feature (fun x => (value x : ℝ)) color := by
  simp only [chartConditionalProgram,Rat.cast_mul,Rat.cast_natCast,chartExpectationProgram_cast,
    conditional_apply,Fintype.card_fin]
  congr 2
  funext x
  split_ifs <;> simp

 theorem chartFeatureProgram_cast (feature : Fin charts → Fin colors) (allowed : Finset (Fin colors))
    (value : Fin charts → ℚ) (chart : Fin charts) :
    (chartFeatureProgram charts colors feature allowed value chart : ℝ)=
      featureProjection (FiniteDist.uniform (Fin charts)) feature allowed (fun x => (value x : ℝ)) chart := by
  simp only [chartFeatureProgram,apply_ite,Rat.cast_sub,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,
    Rat.cast_zero,chartConditionalProgram_cast,featureProjection_apply,centerAllowed_apply]
  split_ifs <;> rfl

 theorem chartProjectionProgram_cast (feature : Fin features → Fin charts → Fin colors)
    (allowed : Fin features → Finset (Fin colors)) (value : Fin charts → ℚ) (chart : Fin charts) :
    (chartProjectionProgram charts colors features feature allowed value chart : ℝ)=
      chartProjection (FiniteDist.uniform (Fin charts)) feature allowed (fun x => (value x : ℝ)) chart := by
  simp only [chartProjectionProgram,Rat.cast_add,Rat.cast_sum,chartExpectationProgram_cast,
    chartFeatureProgram_cast,chartProjection_apply,featureProjection_apply]

 theorem chartDeletionProgram_cast (feature : Fin features → Fin charts → Fin colors)
    (allowed : Fin features → Finset (Fin colors)) (safe : Finset (Fin charts))
    (value : Fin charts → ℚ) (chart : Fin charts) :
    (chartDeletionProgram charts colors features feature allowed safe value chart : ℝ)=
      deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)
        (fun x => (value x : ℝ)) chart := by
  rw [chartDeletionProgram,chartProjectionProgram_cast,deletion_apply]
  apply congrArg (fun f => chartProjection (FiniteDist.uniform (Fin charts)) feature allowed f chart)
  funext x
  simp only [Pi.sub_apply,safeMask_apply]
  split_ifs <;> simp

 theorem chartDeletionMatrixProgram_cast (feature : Fin features → Fin charts → Fin colors)
    (allowed : Fin features → Finset (Fin colors)) (safe : Finset (Fin charts)) :
    realMatrixOperator (chartDeletionMatrixProgram charts colors features feature allowed safe)=
      -(deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)).toLinearMap := by
  apply LinearMap.ext
  intro profile
  funext output
  change (∑input,(chartDeletionMatrixProgram charts colors features feature allowed safe output input : ℝ)*profile input)=_
  simp only [chartDeletionMatrixProgram,Rat.cast_neg,chartDeletionProgram_cast]
  let operator := deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)
  simp only [neg_mul,Finset.sum_neg_distrib]
  congr 1
  calc
    _ = ∑ input,operator (Pi.single input 1) output*profile input := by
      apply Finset.sum_congr rfl
      intro input _
      apply congrArg (fun f => operator f output*profile input)
      funext x
      by_cases hx : x=input
      · subst x
        simp
      · simp only [if_neg hx,Pi.single_eq_of_ne hx,Rat.cast_zero]

    _ = _ := congrFun (V7Calibration.linearMap_basis_matrix operator.toLinearMap profile) output

 theorem chartNeumannProgram_cast (feature : Fin features → Fin charts → Fin colors)
    (allowed : Fin features → Finset (Fin colors)) (safe : Finset (Fin charts))
    (rhs : Fin charts → ℚ) (steps : ℕ) :
    (fun output => ((chartNeumannProgram charts colors features feature allowed safe rhs steps).get output : ℝ))=
      realLinearIteration
        (-(deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)).toLinearMap)
        (fun x => (rhs x : ℝ)) steps := by
  simp only [chartNeumannProgram,cachedLinearIteration_get,linearIteration_cast,chartDeletionMatrixProgram_cast]

end
end AFT.BoundaryCalibration

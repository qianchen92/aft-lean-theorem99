import AFT.MarkedChartProgram

/-! # A materialized chart evaluator with a rational arithmetic counter

The metadata (finite feature and membership tables) are read as arrays.
The counter charges rational addition, subtraction, multiplication, division,
and the branch tests in the displayed evaluator. Integer metadata construction
and binary arithmetic costs are separate bounds.
-/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators

structure ChartArithmetic where
  value : ℚ
  work : ℕ

namespace ChartArithmetic

def literal (value : ℚ) : ChartArithmetic := ⟨value,0⟩
def add (first second : ChartArithmetic) : ChartArithmetic :=
  ⟨first.value+second.value,first.work+second.work+1⟩
def sub (first second : ChartArithmetic) : ChartArithmetic :=
  ⟨first.value-second.value,first.work+second.work+1⟩
def mul (first second : ChartArithmetic) : ChartArithmetic :=
  ⟨first.value*second.value,first.work+second.work+1⟩
def div (first second : ChartArithmetic) : ChartArithmetic :=
  ⟨first.value/second.value,first.work+second.work+1⟩
def test (condition : Bool) (yes no : Unit → ChartArithmetic) : ChartArithmetic :=
  let result := if condition then yes () else no ()
  ⟨result.value,result.work+1⟩
def sum {Index : Type*} [DecidableEq Index] (set : Finset Index) (term : Index → ChartArithmetic) : ChartArithmetic :=
  ⟨∑i∈set,(term i).value,(∑i∈set,(term i).work)+set.card⟩

def expectation (charts : ℕ) (value : Fin charts → ℚ) : ChartArithmetic :=
  (sum Finset.univ (fun i => literal (value i))).div (literal charts)

def conditional (charts colors : ℕ) (feature : Fin charts → Fin colors)
    (value : Fin charts → ℚ) (color : Fin colors) : ChartArithmetic :=
  (literal colors).mul (expectation charts (fun chart => if feature chart=color then value chart else 0))

def feature (charts colors : ℕ) (feature : Fin charts → Fin colors)
    (allowed : Finset (Fin colors)) (value : Fin charts → ℚ) (chart : Fin charts) : ChartArithmetic :=
  test (decide (feature chart∈allowed))
    (fun _ => (conditional charts colors feature value (feature chart)).sub
      ((sum allowed (conditional charts colors feature value)).div (literal allowed.card)))
    (fun _ => literal 0)

def projection (charts colors features : ℕ)
    (featuresMap : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (value : Fin charts → ℚ) (chart : Fin charts) : ChartArithmetic :=
  (expectation charts value).add
    (sum Finset.univ (fun index => feature charts colors (featuresMap index) (allowed index) value chart))

def deletionEntry (charts colors features : ℕ)
    (featuresMap : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (output input : Fin charts) : ChartArithmetic :=
  (literal 0).sub (projection charts colors features featuresMap allowed
    (fun point => if point∈safe then 0 else if point=input then 1 else 0) output)

def defect (charts colors features : ℕ)
    (featuresMap : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (marked : Fin features) (atom : ℚ) (spike : Fin charts → ℚ) (chart : Fin charts) : ChartArithmetic :=
  (literal atom).mul (sum Finset.univ (fun index =>
    test (decide (index=marked)) (fun _ => literal 0)
      (fun _ => feature charts colors (featuresMap index) (allowed index) spike chart)))

@[simp] theorem expectation_value (charts : ℕ) (value : Fin charts → ℚ) :
    (expectation charts value).value=chartExpectationProgram charts value := rfl
@[simp] theorem conditional_value (charts colors : ℕ) (f : Fin charts → Fin colors)
    (value : Fin charts → ℚ) (color : Fin colors) :
    (conditional charts colors f value color).value=chartConditionalProgram charts colors f value color := rfl
@[simp] theorem feature_value (charts colors : ℕ) (f : Fin charts → Fin colors)
    (allowed : Finset (Fin colors)) (value : Fin charts → ℚ) (chart : Fin charts) :
    (feature charts colors f allowed value chart).value=chartFeatureProgram charts colors f allowed value chart := by
  simp only [feature,test,chartFeatureProgram]
  split_ifs <;> simp_all [sub,div,sum,literal,conditional_value]
@[simp] theorem projection_value (charts colors features : ℕ)
    (f : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (value : Fin charts → ℚ) (chart : Fin charts) :
    (projection charts colors features f allowed value chart).value=chartProjectionProgram charts colors features f allowed value chart := by
  simp only [projection,add,sum,expectation_value,feature_value,chartProjectionProgram]
@[simp] theorem deletionEntry_value (charts colors features : ℕ)
    (f : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (output input : Fin charts) :
    (deletionEntry charts colors features f allowed safe output input).value=chartDeletionMatrixProgram charts colors features f allowed safe output input := by
  simp only [deletionEntry,sub,literal,projection_value,chartDeletionMatrixProgram,chartDeletionProgram]
  ring
@[simp] theorem defect_value (charts colors features : ℕ)
    (f : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (marked : Fin features) (atom : ℚ) (spike : Fin charts → ℚ) (chart : Fin charts) :
    (defect charts colors features f allowed marked atom spike chart).value=chartSpikeDefectProgram charts colors features f allowed marked atom spike chart := by
  simp only [defect,mul,literal,sum,chartSpikeDefectProgram]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  by_cases h : index=marked <;> simp [test,h,feature_value]

 theorem expectation_work (charts : ℕ) (value : Fin charts → ℚ) :
    (expectation charts value).work=charts+1 := by simp [expectation,div,sum,literal]
 theorem conditional_work (charts colors : ℕ) (f : Fin charts → Fin colors)
    (value : Fin charts → ℚ) (color : Fin colors) :
    (conditional charts colors f value color).work=charts+2 := by simp [conditional,mul,literal,expectation_work]

 def featureWork (charts colors : ℕ) : ℕ := (colors+1)*(charts+3)+3
 def projectionWork (charts colors features : ℕ) : ℕ := charts+2+features*(featureWork charts colors+1)

 theorem feature_work (charts colors : ℕ) (f : Fin charts → Fin colors)
    (allowed : Finset (Fin colors)) (value : Fin charts → ℚ) (chart : Fin charts) :
    (feature charts colors f allowed value chart).work≤featureWork charts colors := by
  have hc : allowed.card≤colors := by simpa using Finset.card_le_univ allowed
  simp only [feature,test]
  split_ifs
  · simp only [sub,div,sum,literal,conditional_work,Finset.sum_const,smul_eq_mul,Nat.add_zero]
    unfold featureWork
    nlinarith
  · simp only [literal]
    unfold featureWork
    omega

 theorem projection_work (charts colors features : ℕ)
    (f : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (value : Fin charts → ℚ) (chart : Fin charts) :
    (projection charts colors features f allowed value chart).work≤projectionWork charts colors features := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => feature_work charts colors (f i) (allowed i) value chart)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  simp only [projection,add,sum,expectation_work,Finset.card_univ,Fintype.card_fin]
  unfold projectionWork
  nlinarith

 theorem deletionEntry_work (charts colors features : ℕ)
    (f : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (output input : Fin charts) :
    (deletionEntry charts colors features f allowed safe output input).work≤projectionWork charts colors features+1 := by
  simpa only [deletionEntry,sub,literal,Nat.zero_add] using
    Nat.add_le_add_right (projection_work charts colors features f allowed
      (fun point => if point∈safe then 0 else if point=input then 1 else 0) output) 1

 theorem defect_work (charts colors features : ℕ)
    (f : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (marked : Fin features) (atom : ℚ) (spike : Fin charts → ℚ) (chart : Fin charts) :
    (defect charts colors features f allowed marked atom spike chart).work≤features*(featureWork charts colors+2)+1 := by
  have hh (index : Fin features) :
      (test (decide (index=marked)) (fun _ => literal 0)
        (fun _ => feature charts colors (f index) (allowed index) spike chart)).work≤featureWork charts colors+1 := by
    unfold test
    split_ifs
    · simp only [literal];omega
    · exact Nat.add_le_add_right (feature_work charts colors (f index) (allowed index) spike chart) 1
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hh i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  simp only [literal] at hs
  simp only [defect,mul,literal,sum,Nat.zero_add,Finset.card_univ,Fintype.card_fin]
  nlinarith

end ChartArithmetic

/-- The rational source and two Neumann iterates are materialized once. -/
structure CountedChartArray (charts : ℕ) where
  value : Vector ℚ charts
  work : ℕ

def countedMarkedChartWeightProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ) (steps : ℕ) : CountedChartArray charts :=
  let spike := Vector.ofFn (chartSpikeProgram charts survivingFiber)
  let matrix := Vector.ofFn (fun output => Vector.ofFn (fun input =>
    ChartArithmetic.deletionEntry charts colors features feature allowed safe output input))
  let storedMatrix := Vector.ofFn (fun output => Vector.ofFn (fun input => ((matrix.get output).get input).value))
  let defect := Vector.ofFn (ChartArithmetic.defect charts colors features feature allowed marked atom spike.get)
  let base := cachedLinearIteration storedMatrix (Vector.ofFn (fun _ => 1)) steps
  let repair := cachedLinearIteration storedMatrix (Vector.ofFn (fun point => (defect.get point).value)) steps
  ⟨Vector.ofFn (fun point =>
      ((if point∈safe then (1-atom)*base.get point-repair.get point else 0)+atom*spike.get point)/(charts : ℚ)),
    2*charts+(∑ output,∑ input,((matrix.get output).get input).work)+
      (∑ point,(defect.get point).work)+2*cachedIterationWork charts steps+7*charts⟩

 theorem countedMarkedChartWeightProgram_value (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ) (steps : ℕ) :
    (countedMarkedChartWeightProgram charts colors features feature allowed safe survivingFiber marked atom steps).value=
      markedChartWeightProgram charts colors features feature allowed safe survivingFiber marked atom steps := by
  have hspike : (Vector.ofFn (chartSpikeProgram charts survivingFiber)).get=chartSpikeProgram charts survivingFiber := by
    funext point;exact Vector.get_ofFn _ point
  simp only [countedMarkedChartWeightProgram,Vector.get_ofFn,ChartArithmetic.deletionEntry_value,ChartArithmetic.defect_value,hspike,
    markedChartWeightProgram,markedChartDensityProgram,chartNeumannProgram,cachedMatrix]

 def chartArithmeticWork (charts colors features steps : ℕ) : ℕ :=
   9*charts+charts^2*(ChartArithmetic.projectionWork charts colors features+1)+
     charts*(features*(ChartArithmetic.featureWork charts colors+2)+1)+2*cachedIterationWork charts steps

 theorem countedMarkedChartWeightProgram_work (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ) (steps : ℕ) :
    (countedMarkedChartWeightProgram charts colors features feature allowed safe survivingFiber marked atom steps).work≤
      chartArithmeticWork charts colors features steps := by
  have hm := Finset.sum_le_sum (s:=Finset.univ) (fun output _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun input _ =>
      ChartArithmetic.deletionEntry_work charts colors features feature allowed safe output input))
  have hd := Finset.sum_le_sum (s:=Finset.univ) (fun point _ =>
    ChartArithmetic.defect_work charts colors features feature allowed marked atom (chartSpikeProgram charts survivingFiber) point)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hm hd
  have hspike : (Vector.ofFn (chartSpikeProgram charts survivingFiber)).get=chartSpikeProgram charts survivingFiber := by
    funext point;exact Vector.get_ofFn _ point
  simp only [countedMarkedChartWeightProgram,Vector.get_ofFn,hspike]
  unfold chartArithmeticWork
  nlinarith

end AFT.BoundaryCalibration

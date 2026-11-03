import AFT.BinaryMarkedChartCost
import AFT.BinarySeriesPolynomials

/-! Literal polynomial bounds for the complete binary chart repair. -/
namespace AFT.BinaryArithmetic.RationalBits
open Polynomial AFT.BoundaryCalibration AFT.RationalNumerics

noncomputable def chartExpectationHeightPolynomial (charts bits : Polynomial ℕ) : Polynomial ℕ :=
  charts*(bits+1)+charts

noncomputable def chartConditionalHeightPolynomial (charts colors bits : Polynomial ℕ) : Polynomial ℕ :=
  colors+chartExpectationHeightPolynomial charts bits

noncomputable def chartFeatureHeightPolynomial (charts colors bits : Polynomial ℕ) : Polynomial ℕ :=
  chartConditionalHeightPolynomial charts colors bits+colors*(chartConditionalHeightPolynomial charts colors bits+1)+colors+1

noncomputable def chartProjectionHeightPolynomial (charts colors features bits : Polynomial ℕ) : Polynomial ℕ :=
  chartExpectationHeightPolynomial charts bits+features*(chartFeatureHeightPolynomial charts colors bits+1)+1

noncomputable def chartStoredHeightPolynomial (charts colors features atomBits : Polynomial ℕ) : Polynomial ℕ :=
  chartProjectionHeightPolynomial charts colors features 0+atomBits+features*(chartFeatureHeightPolynomial charts colors (2*charts)+1)

noncomputable def chartIterateHeightPolynomial (charts colors features atomBits steps : Polynomial ℕ) : Polynomial ℕ :=
  steps*((3*(charts^2+charts)+1)*chartStoredHeightPolynomial charts colors features atomBits+charts+1)

noncomputable def finiteSumWorkPolynomial (count bits termWork : Polynomial ℕ) : Polynomial ℕ :=
  count*(termWork+primitiveWorkPolynomial ((count+1)*(bits+1))+2)+2

noncomputable def expectationWorkPolynomial (charts bits termWork : Polynomial ℕ) : Polynomial ℕ :=
  finiteSumWorkPolynomial charts bits termWork+60*(charts+1)^2+
    2*primitiveWorkPolynomial ((charts+1)*(bits+1)+charts+1)+5

noncomputable def conditionalWorkPolynomial (charts colors bits : Polynomial ℕ) : Polynomial ℕ :=
  expectationWorkPolynomial charts bits (6*charts+6*colors+10)+60*(colors+1)^2+
    primitiveWorkPolynomial (chartConditionalHeightPolynomial charts colors bits+1)+3

noncomputable def featureWorkPolynomial (charts colors bits : Polynomial ℕ) : Polynomial ℕ :=
  let H := chartConditionalHeightPolynomial charts colors bits
  conditionalWorkPolynomial charts colors bits+
    finiteSumWorkPolynomial colors H (conditionalWorkPolynomial charts colors bits+3*colors+5)+
    colors*(3*colors+6)+60*(colors+1)^2+3*charts+3*colors+
    2*primitiveWorkPolynomial (colors*(H+1)+colors+1)+
    2*primitiveWorkPolynomial (chartFeatureHeightPolynomial charts colors bits)+30

noncomputable def projectionWorkPolynomial (charts colors features bits : Polynomial ℕ) : Polynomial ℕ :=
  expectationWorkPolynomial charts bits (3*charts+3)+
    finiteSumWorkPolynomial features (chartFeatureHeightPolynomial charts colors bits)
      (featureWorkPolynomial charts colors bits+6*features+charts+colors+9)+
    primitiveWorkPolynomial (chartProjectionHeightPolynomial charts colors features bits)+3

noncomputable def spikeWorkPolynomial (charts : Polynomial ℕ) : Polynomial ℕ :=
  3*charts+charts*(3*charts+6)+120*(charts+1)^2+2*primitiveWorkPolynomial charts+12

noncomputable def deletionEntryWorkPolynomial (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  charts*(9*charts+10)+projectionWorkPolynomial charts colors features 0+primitiveWorkPolynomial 0+5

noncomputable def deletionMatrixWorkPolynomial (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  charts*(charts*(deletionEntryWorkPolynomial charts colors features+2)+4)+2

noncomputable def defectWorkPolynomial (charts colors features atomBits : Polynomial ℕ) : Polynomial ℕ :=
  finiteSumWorkPolynomial features (chartFeatureHeightPolynomial charts colors (2*charts))
     (featureWorkPolynomial charts colors (2*charts)+12*features+charts+colors+13)+
   primitiveWorkPolynomial (atomBits+features*(chartFeatureHeightPolynomial charts colors (2*charts)+1))+2

noncomputable def iterationBitsPolynomial (count bits limit : Polynomial ℕ) : Polynomial ℕ :=
  bits+limit*((3*(count^2+count)+1)*bits+count+1)

noncomputable def matrixRowWorkPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(10*count+13+primitiveWorkPolynomial bits+primitiveWorkPolynomial ((count+1)*(2*bits+1))+2)+2

noncomputable def matrixApplyWorkPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(matrixRowWorkPolynomial count bits+2)+2

noncomputable def iterationWorkStepPolynomial (count bits limit : Polynomial ℕ) : Polynomial ℕ :=
  matrixApplyWorkPolynomial count (iterationBitsPolynomial count bits limit)+
    count*(6*count+13+2*primitiveWorkPolynomial ((count+1)*(2*iterationBitsPolynomial count bits limit+1)))+5

noncomputable def chartEntryBitsPolynomial (charts atomBits iterateBits : Polynomial ℕ) : Polynomial ℕ :=
  2*iterateBits+2*atomBits+3*charts+10

noncomputable def chartWeightEntryWorkPolynomial (charts atomBits iterateBits : Polynomial ℕ) : Polynomial ℕ :=
  12*charts+40+10*primitiveWorkPolynomial (chartEntryBitsPolynomial charts atomBits iterateBits)+60*(charts+1)^2

noncomputable def markedChartWorkPolynomial (charts colors features atomBits steps : Polynomial ℕ) : Polynomial ℕ :=
  charts*(spikeWorkPolynomial charts+2)+2+deletionMatrixWorkPolynomial charts colors features+
     charts*(defectWorkPolynomial charts colors features atomBits+2)+2+
     2*(steps*iterationWorkStepPolynomial charts (chartStoredHeightPolynomial charts colors features atomBits) steps+2*charts+2)+
     charts*(chartWeightEntryWorkPolynomial charts atomBits (chartIterateHeightPolynomial charts colors features atomBits steps)+2)+
     2*charts+9

@[simp] theorem chartExpectationHeightPolynomial_eval (charts bits : Polynomial ℕ) (n : ℕ) :
    (chartExpectationHeightPolynomial charts bits).eval n=chartExpectationHeight (charts.eval n) (bits.eval n) := by
  simp [chartExpectationHeightPolynomial,chartExpectationHeight]

@[simp] theorem chartConditionalHeightPolynomial_eval (charts colors bits : Polynomial ℕ) (n : ℕ) :
    (chartConditionalHeightPolynomial charts colors bits).eval n=chartConditionalHeight (charts.eval n) (colors.eval n) (bits.eval n) := by
  simp [chartConditionalHeightPolynomial,chartConditionalHeight]

@[simp] theorem chartFeatureHeightPolynomial_eval (charts colors bits : Polynomial ℕ) (n : ℕ) :
    (chartFeatureHeightPolynomial charts colors bits).eval n=chartFeatureHeight (charts.eval n) (colors.eval n) (bits.eval n) := by
  simp [chartFeatureHeightPolynomial,chartFeatureHeight]

@[simp] theorem chartProjectionHeightPolynomial_eval (charts colors features bits : Polynomial ℕ) (n : ℕ) :
    (chartProjectionHeightPolynomial charts colors features bits).eval n=chartProjectionHeight (charts.eval n) (colors.eval n) (features.eval n) (bits.eval n) := by
  simp [chartProjectionHeightPolynomial,chartProjectionHeight]

@[simp] theorem chartStoredHeightPolynomial_eval (charts colors features atomBits : Polynomial ℕ) (n : ℕ) :
    (chartStoredHeightPolynomial charts colors features atomBits).eval n=chartStoredHeight (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) := by
  simp [chartStoredHeightPolynomial,chartStoredHeight]

@[simp] theorem chartIterateHeightPolynomial_eval (charts colors features atomBits steps : Polynomial ℕ) (n : ℕ) :
    (chartIterateHeightPolynomial charts colors features atomBits steps).eval n=chartIterateHeight (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) (steps.eval n) := by
  simp [chartIterateHeightPolynomial,chartIterateHeight]

@[simp] theorem finiteSumWorkPolynomial_eval (count bits termWork : Polynomial ℕ) (n : ℕ) :
    (finiteSumWorkPolynomial count bits termWork).eval n=finiteSumWork (count.eval n) (bits.eval n) (termWork.eval n) := by
  simp [finiteSumWorkPolynomial,finiteSumWork]

@[simp] theorem expectationWorkPolynomial_eval (charts bits termWork : Polynomial ℕ) (n : ℕ) :
    (expectationWorkPolynomial charts bits termWork).eval n=expectationWork (charts.eval n) (bits.eval n) (termWork.eval n) := by
  simp [expectationWorkPolynomial,expectationWork]

@[simp] theorem conditionalWorkPolynomial_eval (charts colors bits : Polynomial ℕ) (n : ℕ) :
    (conditionalWorkPolynomial charts colors bits).eval n=conditionalWork (charts.eval n) (colors.eval n) (bits.eval n) := by
  simp [conditionalWorkPolynomial,conditionalWork]

@[simp] theorem featureWorkPolynomial_eval (charts colors bits : Polynomial ℕ) (n : ℕ) :
    (featureWorkPolynomial charts colors bits).eval n=featureWork (charts.eval n) (colors.eval n) (bits.eval n) := by
  simp [featureWorkPolynomial,featureWork]

@[simp] theorem projectionWorkPolynomial_eval (charts colors features bits : Polynomial ℕ) (n : ℕ) :
    (projectionWorkPolynomial charts colors features bits).eval n=projectionWork (charts.eval n) (colors.eval n) (features.eval n) (bits.eval n) := by
  simp [projectionWorkPolynomial,projectionWork]

@[simp] theorem spikeWorkPolynomial_eval (charts : Polynomial ℕ) (n : ℕ) :
    (spikeWorkPolynomial charts).eval n=spikeWork (charts.eval n) := by
  simp [spikeWorkPolynomial,spikeWork]

@[simp] theorem deletionEntryWorkPolynomial_eval (charts colors features : Polynomial ℕ) (n : ℕ) :
    (deletionEntryWorkPolynomial charts colors features).eval n=deletionEntryWork (charts.eval n) (colors.eval n) (features.eval n) := by
  simp [deletionEntryWorkPolynomial,deletionEntryWork]

@[simp] theorem deletionMatrixWorkPolynomial_eval (charts colors features : Polynomial ℕ) (n : ℕ) :
    (deletionMatrixWorkPolynomial charts colors features).eval n=deletionMatrixWork (charts.eval n) (colors.eval n) (features.eval n) := by
  simp [deletionMatrixWorkPolynomial,deletionMatrixWork]

@[simp] theorem defectWorkPolynomial_eval (charts colors features atomBits : Polynomial ℕ) (n : ℕ) :
    (defectWorkPolynomial charts colors features atomBits).eval n=defectWork (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) := by
  simp [defectWorkPolynomial,defectWork]

@[simp] theorem iterationBitsPolynomial_eval (count bits limit : Polynomial ℕ) (n : ℕ) :
    (iterationBitsPolynomial count bits limit).eval n=iterationBits (count.eval n) (bits.eval n) (limit.eval n) := by
  simp [iterationBitsPolynomial,iterationBits]

@[simp] theorem matrixRowWorkPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (matrixRowWorkPolynomial count bits).eval n=matrixRowWork (count.eval n) (bits.eval n) := by
  simp [matrixRowWorkPolynomial,matrixRowWork]

@[simp] theorem matrixApplyWorkPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (matrixApplyWorkPolynomial count bits).eval n=matrixApplyWork (count.eval n) (bits.eval n) := by
  simp [matrixApplyWorkPolynomial,matrixApplyWork]

@[simp] theorem iterationWorkStepPolynomial_eval (count bits limit : Polynomial ℕ) (n : ℕ) :
    (iterationWorkStepPolynomial count bits limit).eval n=iterationWorkStep (count.eval n) (bits.eval n) (limit.eval n) := by
  simp [iterationWorkStepPolynomial,iterationWorkStep]

@[simp] theorem chartEntryBitsPolynomial_eval (charts atomBits iterateBits : Polynomial ℕ) (n : ℕ) :
    (chartEntryBitsPolynomial charts atomBits iterateBits).eval n=chartEntryBits (charts.eval n) (atomBits.eval n) (iterateBits.eval n) := by
  simp [chartEntryBitsPolynomial,chartEntryBits]

@[simp] theorem chartWeightEntryWorkPolynomial_eval (charts atomBits iterateBits : Polynomial ℕ) (n : ℕ) :
    (chartWeightEntryWorkPolynomial charts atomBits iterateBits).eval n=chartWeightEntryWork (charts.eval n) (atomBits.eval n) (iterateBits.eval n) := by
  simp [chartWeightEntryWorkPolynomial,chartWeightEntryWork]

@[simp] theorem markedChartWorkPolynomial_eval (charts colors features atomBits steps : Polynomial ℕ) (n : ℕ) :
    (markedChartWorkPolynomial charts colors features atomBits steps).eval n=markedChartWork (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) (steps.eval n) := by
  simp [markedChartWorkPolynomial,markedChartWork]

set_option maxHeartbeats 2000000 in
theorem markedChartWork_mono {c1 c2 q1 q2 f1 f2 b1 b2 s1 s2 : ℕ}
    (hc : c1≤c2) (hq : q1≤q2) (hf : f1≤f2) (hb : b1≤b2) (hs : s1≤s2) :
    markedChartWork c1 q1 f1 b1 s1 ≤ markedChartWork c2 q2 f2 b2 s2 := by
  simp only [markedChartWork,spikeWork,deletionMatrixWork,deletionEntryWork,projectionWork,expectationWork,conditionalWork,featureWork,finiteSumWork,defectWork,iterationWorkStep,matrixApplyWork,matrixRowWork,iterationBits,chartWeightEntryWork,chartEntryBits,chartIterateHeight,chartStoredHeight,chartProjectionHeight,chartFeatureHeight,chartConditionalHeight,chartExpectationHeight,primitiveWorkBound]
  gcongr

theorem markedChartWeight_polynomial_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (safe fiber : Vector Bool charts) (marked : Fin features) (atom : RationalBits) (bits steps : ℕ)
    (hatom : HeightBound atom.decode bits)
    (chartBudget colorBudget featureBudget bitBudget stepBudget : Polynomial ℕ) (n : ℕ)
    (hc : charts≤chartBudget.eval n) (hq : colors≤colorBudget.eval n)
    (hf : features≤featureBudget.eval n) (hb : bits≤bitBudget.eval n) (hs : steps≤stepBudget.eval n) :
    (markedChartWeight feature allowed safe fiber marked atom steps).work ≤
      (markedChartWorkPolynomial chartBudget colorBudget featureBudget bitBudget stepBudget).eval n := by
  rw [markedChartWorkPolynomial_eval]
  exact (markedChartWeight_work feature allowed safe fiber marked atom bits steps hatom).trans
    (markedChartWork_mono hc hq hf hb hs)

end AFT.BinaryArithmetic.RationalBits

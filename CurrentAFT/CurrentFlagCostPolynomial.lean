import CurrentAFT.CurrentFlagChartDraw
import AFT.BinaryProtectedPolynomialBound

/-! Actual cost polynomial of the current all-line flag repair and draw. -/
namespace CurrentAFT.CurrentFlagCostPolynomial
open AFT BinaryArithmetic BinaryArithmetic.RationalBits BoundaryCalibration RationalNumerics Polynomial
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def metadata (cutoff modulus baseline : Polynomial ℕ) : Polynomial ℕ :=
  let charts := modulus*(modulus*modulus)
  let features := (2*cutoff+1)*(2*cutoff+1)
  let onLine := 3*cutoff+1+500*(features+(2*cutoff+1)+2)^2+3*(features+cutoff)+5
  let fiber := features*(9*features+4*charts+4*modulus+23)+9*charts+12*modulus+25
  protectedMetadataWorkPolynomial cutoff modulus 1 baseline+(features*(onLine+2)+2)+
    2*(charts*(protectedScaleWorkPolynomial modulus charts+6)+2)+(charts*(fiber+2)+2)+5

def targetHeight (charts colors features atomBits spikeBits : Polynomial ℕ) : Polynomial ℕ :=
  2*atomBits+features*(chartFeatureHeightPolynomial charts colors spikeBits+1)+2

def storedHeight (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  chartProjectionHeightPolynomial charts colors features 0+targetHeight charts colors features 1 (2*charts)

def iterateHeight (charts colors features steps : Polynomial ℕ) : Polynomial ℕ :=
  steps*((3*(charts^2+charts)+1)*storedHeight charts colors features+charts+1)

def targetWork (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  finiteSumWorkPolynomial features (chartFeatureHeightPolynomial charts colors (2*charts))
    (featureWorkPolynomial charts colors (2*charts)+12*features+charts+colors+13)+
    7*primitiveWorkPolynomial (targetHeight charts colors features 1 (2*charts))+11

def regularWork (charts colors features steps : Polynomial ℕ) : Polynomial ℕ :=
  (charts*(spikeWorkPolynomial charts+2)+2)+deletionMatrixWorkPolynomial charts colors features+
    (charts*(targetWork charts colors features+2)+2)+
    (steps*iterationWorkStepPolynomial charts (storedHeight charts colors features) steps+2*charts+2)+
    (charts*(6*charts+10)+2)+5

def scaleWork (charts height : Polynomial ℕ) : Polynomial ℕ :=
  charts*(3*charts+3+60*(charts+1)^2+2*primitiveWorkPolynomial (height+charts)+5+2)+2

def drawWork (charts height bits : Polynomial ℕ) : Polynomial ℕ :=
  binaryPositiveDrawPolynomial charts height bits+7*charts+13

def current (cutoff modulus baseline precision bits : Polynomial ℕ) : Polynomial ℕ :=
  let charts := modulus*(modulus*modulus)
  let features := (2*cutoff+1)*(2*cutoff+1)
  let steps := precision+(4*(2*cutoff+1)^2+4)
  let height := iterateHeight charts modulus features steps
  let storedMetadata := metadata cutoff modulus baseline
  let regular := storedMetadata+(storedMetadata+C CurrentFlagPublicProgram.half.work+regularWork charts modulus features steps+3+
    scaleWork charts height+2)+drawWork charts (height+charts) bits+3
  let marked := storedMetadata+(storedMetadata+(charts*(spikeWorkPolynomial charts+2)+2)+scaleWork charts (2*charts)+3)+
    drawWork charts (3*charts) bits+3
  regular+marked+2+protectedScaleWorkPolynomial modulus charts+6

theorem current_eval (cutoff modulus baseline precision bits : Polynomial ℕ) (security : ℕ) :
    (current cutoff modulus baseline precision bits).eval security =
      CurrentFlagChartDraw.workBound (cutoff.eval security) (modulus.eval security) (baseline.eval security)
        (precision.eval security) (bits.eval security) := by
  simp only [current, metadata, targetHeight, storedHeight, iterateHeight, targetWork, regularWork, scaleWork, drawWork,
    eval_add, eval_mul, eval_pow, eval_ofNat, eval_one, eval_zero, eval_C,
    protectedMetadataWorkPolynomial_eval, protectedScaleWorkPolynomial_eval,
    chartFeatureHeightPolynomial_eval, chartProjectionHeightPolynomial_eval,
    featureWorkPolynomial_eval, finiteSumWorkPolynomial_eval, primitiveWorkPolynomial_eval,
    spikeWorkPolynomial_eval, deletionMatrixWorkPolynomial_eval, iterationWorkStepPolynomial_eval,
    binaryPositiveDrawPolynomial_eval,
    CurrentFlagChartDraw.workBound, CurrentFlagJointDraw.workBound,
    CurrentFlagBranchDraw.regularWork, CurrentFlagBranchDraw.markedWork,
    CurrentFlagWeightArray.regularWeightWork, CurrentFlagWeightArray.markedWeightWork,
    CurrentFlagWeightArray.regularWeightHeight, CurrentFlagWeightArray.scaleWork, CurrentFlagWeightArray.entryWork,
    CurrentFlagPublicProgram.workBound, CurrentFlagBinaryMetadata.workBound,
    CurrentFlagBinaryMasks.onLineWork, CurrentFlagBinaryMasks.fiberWork, CurrentFlagBinary.regularWork,
    CurrentFlagBinary.targetWork, CurrentFlagBinary.offLineWork, CurrentFlagBinary.defectTermWork,
    CurrentFlagBinary.targetHeight, CurrentFlagBinary.defectHeight, CurrentFlagBinary.storedHeight,
    CurrentFlagBinary.iterateHeight, CurrentFlagDraw.workBound, CurrentFlagTargetNorm.precisionSteps]

theorem work_mono {cutoff upper modulus q baseline height precision steps bits more : ℕ}
    (hc : cutoff ≤ upper) (hq : modulus ≤ q) (hh : baseline ≤ height)
    (hp : precision ≤ steps) (hb : bits ≤ more) :
    CurrentFlagChartDraw.workBound cutoff modulus baseline precision bits ≤
      CurrentFlagChartDraw.workBound upper q height steps more := by
  simp only [CurrentFlagChartDraw.workBound, CurrentFlagJointDraw.workBound,
    CurrentFlagBranchDraw.regularWork, CurrentFlagBranchDraw.markedWork,
    CurrentFlagWeightArray.regularWeightWork, CurrentFlagWeightArray.markedWeightWork,
    CurrentFlagWeightArray.regularWeightHeight, CurrentFlagWeightArray.scaleWork, CurrentFlagWeightArray.entryWork,
    CurrentFlagPublicProgram.workBound, CurrentFlagBinaryMetadata.workBound,
    CurrentFlagBinaryMasks.onLineWork, CurrentFlagBinaryMasks.fiberWork, CurrentFlagBinary.regularWork,
    CurrentFlagBinary.targetWork, CurrentFlagBinary.offLineWork, CurrentFlagBinary.defectTermWork,
    CurrentFlagBinary.targetHeight, CurrentFlagBinary.defectHeight, CurrentFlagBinary.storedHeight,
    CurrentFlagBinary.iterateHeight, CurrentFlagDraw.workBound, CurrentFlagTargetNorm.precisionSteps,
    protectedMetadataWork, protectedMetadataCoreWork, protectedDimensionsWork, protectedFeatureWork,
    modularDifferenceWork, protectedPaletteWork, protectedScaleWork, supportWork,
    chartFeatureHeight, chartProjectionHeight, chartConditionalHeight, chartExpectationHeight,
    finiteSumWork, featureWork, conditionalWork, expectationWork, spikeWork, deletionMatrixWork,
    deletionEntryWork, projectionWork, iterationWorkStep, iterationBits, matrixApplyWork, matrixRowWork,
    binaryPositiveDrawWork, binaryPositiveNormalizeWork, normalizeArrayWork, sumArrayWork,
    binaryRationalDrawWork, ticketTableWork, ticketTableDigitBound, dyadicFloorWork, sumDigitsWork, primitiveWorkBound]
  gcongr

end
end CurrentAFT.CurrentFlagCostPolynomial

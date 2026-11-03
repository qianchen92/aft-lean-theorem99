import AFT.BinarySafeProtectedChart
import AFT.BinaryChartPolynomials
import AFT.BinarySamplingPolynomials

/-! Literal natural-coefficient polynomial costs for all protected metadata,
binary repair, finite sampling, and legal fallback. -/
namespace AFT.BinaryArithmetic
open Polynomial RationalBits AFT.BoundaryCalibration

noncomputable def modularDifferenceWorkPolynomial (address cutoff modulus : Polynomial ℕ) : Polynomial ℕ :=
  500*(cutoff+modulus+2)^2+2*modulus+2*address+6+
     500*(address+2*modulus+2)^2

@[simp] theorem modularDifferenceWorkPolynomial_eval (address cutoff modulus : Polynomial ℕ) (n : ℕ) :
    (modularDifferenceWorkPolynomial address cutoff modulus).eval n=modularDifferenceWork (address.eval n) (cutoff.eval n) (modulus.eval n) := by
  simp [modularDifferenceWorkPolynomial,modularDifferenceWork]

noncomputable def protectedFeatureWorkPolynomial (cutoff modulus input chart : Polynomial ℕ) : Polynomial ℕ :=
  3*cutoff+1+500*(input+(2*cutoff+1)+2)^2+
   (modulus*(2*modulus+3)+1)+500*(chart+modulus*modulus+2)^2+
   500*(modulus*modulus+modulus+2)^2+
   modularDifferenceWorkPolynomial input cutoff modulus+modularDifferenceWorkPolynomial (2*cutoff+1) cutoff modulus+
   (modulus*modulus*(2*modulus+3)+1)+(modulus*(2*modulus+3)+1)+
   (2*chart+1)+(2*(chart+modulus*modulus*modulus)+1)+
   500*(chart+modulus*modulus*modulus+modulus*modulus+modulus+2)^2+13

@[simp] theorem protectedFeatureWorkPolynomial_eval (cutoff modulus input chart : Polynomial ℕ) (n : ℕ) :
    (protectedFeatureWorkPolynomial cutoff modulus input chart).eval n=protectedFeatureWork (cutoff.eval n) (modulus.eval n) (input.eval n) (chart.eval n) := by
  simp [protectedFeatureWorkPolynomial,protectedFeatureWork]

noncomputable def protectedPaletteWorkPolynomial (cutoff modulus input color boundaryBits baselineBits : Polynomial ℕ) : Polynomial ℕ :=
  3*cutoff+1+500*(input+(2*cutoff+1)+2)^2+
     50*(2*cutoff+2)^2+50*(cutoff+1)^2+50*(modulus+1)^2+50*(color+1)^2+
     200*(boundaryBits+baselineBits+3*cutoff+modulus+color+10)+200

@[simp] theorem protectedPaletteWorkPolynomial_eval (cutoff modulus input color boundaryBits baselineBits : Polynomial ℕ) (n : ℕ) :
    (protectedPaletteWorkPolynomial cutoff modulus input color boundaryBits baselineBits).eval n=protectedPaletteWork (cutoff.eval n) (modulus.eval n) (input.eval n) (color.eval n) (boundaryBits.eval n) (baselineBits.eval n) := by
  simp [protectedPaletteWorkPolynomial,protectedPaletteWork]

noncomputable def protectedScaleWorkPolynomial (modulus chart : Polynomial ℕ) : Polynomial ℕ :=
  modulus*(2*modulus+3)+1+500*(chart+modulus*modulus+2)^2+
     500*(modulus*modulus+modulus+2)^2+3

@[simp] theorem protectedScaleWorkPolynomial_eval (modulus chart : Polynomial ℕ) (n : ℕ) :
    (protectedScaleWorkPolynomial modulus chart).eval n=protectedScaleWork (modulus.eval n) (chart.eval n) := by
  simp [protectedScaleWorkPolynomial,protectedScaleWork]

noncomputable def supportWorkPolynomial (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  features*(12*features+4*charts+4*colors+22)+features*features+5*features+7*charts+9*colors+32

@[simp] theorem supportWorkPolynomial_eval (charts colors features : Polynomial ℕ) (n : ℕ) :
    (supportWorkPolynomial charts colors features).eval n=supportWork (charts.eval n) (colors.eval n) (features.eval n) := by
  simp [supportWorkPolynomial,supportWork]

noncomputable def protectedDimensionsWorkPolynomial (cutoff modulus : Polynomial ℕ) : Polynomial ℕ :=
  3*cutoff+1+(2*cutoff+1)*(2*(2*cutoff+1)+3)+1+
     modulus*(2*modulus+3)+1+modulus*(2*(modulus*modulus)+3)+1+5

@[simp] theorem protectedDimensionsWorkPolynomial_eval (cutoff modulus : Polynomial ℕ) (n : ℕ) :
    (protectedDimensionsWorkPolynomial cutoff modulus).eval n=protectedDimensionsWork (cutoff.eval n) (modulus.eval n) := by
  simp [protectedDimensionsWorkPolynomial,protectedDimensionsWork]

noncomputable def protectedMetadataCoreWorkPolynomial (cutoff modulus charts features boundaryBits baselineBits : Polynomial ℕ) : Polynomial ℕ :=
  features*(charts*(protectedFeatureWorkPolynomial cutoff modulus features charts+2)+4)+2+
     features*(modulus*(protectedPaletteWorkPolynomial cutoff modulus features modulus boundaryBits baselineBits+2)+4)+2+
     charts*(protectedScaleWorkPolynomial modulus charts+2)+2+
     (3*cutoff+1+(2*cutoff+1)*(2*cutoff+3)+1+2*cutoff+1+4)+
     2*(charts*(supportWorkPolynomial charts modulus features+2)+2)+4*charts+8

@[simp] theorem protectedMetadataCoreWorkPolynomial_eval (cutoff modulus charts features boundaryBits baselineBits : Polynomial ℕ) (n : ℕ) :
    (protectedMetadataCoreWorkPolynomial cutoff modulus charts features boundaryBits baselineBits).eval n=protectedMetadataCoreWork (cutoff.eval n) (modulus.eval n) (charts.eval n) (features.eval n) (boundaryBits.eval n) (baselineBits.eval n) := by
  simp [protectedMetadataCoreWorkPolynomial,protectedMetadataCoreWork]

noncomputable def protectedMetadataWorkPolynomial (cutoff modulus boundaryBits baselineBits : Polynomial ℕ) : Polynomial ℕ :=
  protectedDimensionsWorkPolynomial cutoff modulus+
     protectedMetadataCoreWorkPolynomial cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) boundaryBits baselineBits+2

@[simp] theorem protectedMetadataWorkPolynomial_eval (cutoff modulus boundaryBits baselineBits : Polynomial ℕ) (n : ℕ) :
    (protectedMetadataWorkPolynomial cutoff modulus boundaryBits baselineBits).eval n=protectedMetadataWork (cutoff.eval n) (modulus.eval n) (boundaryBits.eval n) (baselineBits.eval n) := by
  simp [protectedMetadataWorkPolynomial,protectedMetadataWork]

noncomputable def protectedAtomHeightPolynomial (cutoff : Polynomial ℕ) : Polynomial ℕ :=
  100*((2*cutoff+1)*(2*cutoff+1))

@[simp] theorem protectedAtomHeightPolynomial_eval (cutoff : Polynomial ℕ) (n : ℕ) :
    (protectedAtomHeightPolynomial cutoff).eval n=protectedAtomHeight (cutoff.eval n) := by
  simp [protectedAtomHeightPolynomial,protectedAtomHeight]

noncomputable def protectedAtomWorkPolynomial (cutoff : Polynomial ℕ) : Polynomial ℕ :=
  3*cutoff+1+(2*cutoff+1)*(2*(2*cutoff+1)+3)+1+
     100*(2*((2*cutoff+1)*(2*cutoff+1))+3)+1+
     60*(protectedAtomHeightPolynomial cutoff+1)^2+2*primitiveWorkPolynomial (protectedAtomHeightPolynomial cutoff)+7

@[simp] theorem protectedAtomWorkPolynomial_eval (cutoff : Polynomial ℕ) (n : ℕ) :
    (protectedAtomWorkPolynomial cutoff).eval n=protectedAtomWork (cutoff.eval n) := by
  simp [protectedAtomWorkPolynomial,protectedAtomWork]

noncomputable def chartWeightHeightPolynomial (charts colors features atomBits steps : Polynomial ℕ) : Polynomial ℕ :=
  2*chartIterateHeightPolynomial charts colors features atomBits steps+2*atomBits+3*charts+3

@[simp] theorem chartWeightHeightPolynomial_eval (charts colors features atomBits steps : Polynomial ℕ) (n : ℕ) :
    (chartWeightHeightPolynomial charts colors features atomBits steps).eval n=chartWeightHeight (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) (steps.eval n) := by
  simp [chartWeightHeightPolynomial,chartWeightHeight]

noncomputable def protectedChartWeightHeightPolynomial (cutoff modulus steps : Polynomial ℕ) : Polynomial ℕ :=
  chartWeightHeightPolynomial (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) (protectedAtomHeightPolynomial cutoff) steps

@[simp] theorem protectedChartWeightHeightPolynomial_eval (cutoff modulus steps : Polynomial ℕ) (n : ℕ) :
    (protectedChartWeightHeightPolynomial cutoff modulus steps).eval n=protectedChartWeightHeight (cutoff.eval n) (modulus.eval n) (steps.eval n) := by
  simp [protectedChartWeightHeightPolynomial,protectedChartWeightHeight]

noncomputable def protectedChartWeightWorkPolynomial (cutoff modulus boundaryBits baselineBits steps : Polynomial ℕ) : Polynomial ℕ :=
  protectedMetadataWorkPolynomial cutoff modulus boundaryBits baselineBits+
     (3*cutoff+1+(2*cutoff+1)*(2*cutoff+3)+1+2*cutoff+1+4)+protectedAtomWorkPolynomial cutoff+
     markedChartWorkPolynomial (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) (protectedAtomHeightPolynomial cutoff) steps+4

@[simp] theorem protectedChartWeightWorkPolynomial_eval (cutoff modulus boundaryBits baselineBits steps : Polynomial ℕ) (n : ℕ) :
    (protectedChartWeightWorkPolynomial cutoff modulus boundaryBits baselineBits steps).eval n=protectedChartWeightWork (cutoff.eval n) (modulus.eval n) (boundaryBits.eval n) (baselineBits.eval n) (steps.eval n) := by
  simp [protectedChartWeightWorkPolynomial,protectedChartWeightWork]

noncomputable def binaryProtectedChartDrawWorkPolynomial (cutoff modulus boundaryBits baselineBits steps bits : Polynomial ℕ) : Polynomial ℕ :=
  protectedChartWeightWorkPolynomial cutoff modulus boundaryBits baselineBits steps+
    binaryPositiveDrawPolynomial (modulus*(modulus*modulus)) (protectedChartWeightHeightPolynomial cutoff modulus steps) bits+2

@[simp] theorem binaryProtectedChartDrawWorkPolynomial_eval (cutoff modulus boundaryBits baselineBits steps bits : Polynomial ℕ) (n : ℕ) :
    (binaryProtectedChartDrawWorkPolynomial cutoff modulus boundaryBits baselineBits steps bits).eval n=binaryProtectedChartDrawWork (cutoff.eval n) (modulus.eval n) (boundaryBits.eval n) (baselineBits.eval n) (steps.eval n) (bits.eval n) := by
  simp [binaryProtectedChartDrawWorkPolynomial,binaryProtectedChartDrawWork]

noncomputable def binarySafeProtectedChartWorkPolynomial (cutoff modulus boundaryBits baselineBits steps bits : Polynomial ℕ) : Polynomial ℕ :=
  binaryProtectedChartDrawWorkPolynomial cutoff modulus boundaryBits baselineBits steps bits+
    protectedMetadataWorkPolynomial cutoff modulus boundaryBits baselineBits+7*(modulus*(modulus*modulus))+11

@[simp] theorem binarySafeProtectedChartWorkPolynomial_eval (cutoff modulus boundaryBits baselineBits steps bits : Polynomial ℕ) (n : ℕ) :
    (binarySafeProtectedChartWorkPolynomial cutoff modulus boundaryBits baselineBits steps bits).eval n=binarySafeProtectedChartWork (cutoff.eval n) (modulus.eval n) (boundaryBits.eval n) (baselineBits.eval n) (steps.eval n) (bits.eval n) := by
  simp [binarySafeProtectedChartWorkPolynomial,binarySafeProtectedChartWork]

end AFT.BinaryArithmetic

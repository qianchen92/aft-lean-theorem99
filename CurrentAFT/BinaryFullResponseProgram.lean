import CurrentAFT.BinaryFullResponseData
import CurrentAFT.BinaryPackedRootUniform
import CurrentAFT.BinaryRootMetadataSerializer
import CurrentAFT.BinaryControlChoiceAverage
import CurrentAFT.CountedBoundedRootTags
import CurrentAFT.BinaryBackgroundPopulation

/-! # The actual full-response algorithm from finite stored metadata

Each root set is generated once as an increasing bounded sublist. Every
control selection is averaged with its actual without-replacement mass.
The common queue is averaged only after multiplying by its background.
-/
namespace CurrentAFT.BinaryFullResponseProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct BinaryFullResponseData
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev Data (order : ℕ) := BinaryFullResponseData.Data order
abbrev Color (security : ℕ) := BinaryWeightedPointKernel.Color security
abbrev PrimaryPool (security : ℕ) := BinaryControlChoiceAverage.PrimaryPool security
abbrev BodyPool (security : ℕ) := BinaryControlChoiceAverage.BodyPool security
abbrev Tag (security order : ℕ) := CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order

def tagged (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (primary : Vector (PrimaryPool security) source.val.1.val) (body : Vector (BodyPool security) source.val.2.val)
    (tag : Tag security order) : CoefficientProgram order := fun output inputs centers =>
  let counts := BinaryFullResponseCounts.current security
  let stored := tag.store
  let native : Vector (Fin (BinaryRootMetadataSerializer.population counts.leg counts.ordinary counts.queue)) tag.values.length :=
    Eq.mpr (congrArg (fun count => Vector (Fin count) tag.values.length) (BinaryFullResponseCounts.body_decomposition security)) stored.value
  let metadata := BinaryRootMetadataSerializer.current primary body native
  let result := BinaryPackedRootUniform.current security bits order data.groups data.points queue source metadata.data sourcePrimary sourceBody output inputs centers
  ⟨result.value,counts.work+stored.work+metadata.work+result.work+4⟩

def emptyTag (security order : ℕ) : Tag security order := ⟨[],by simp,Nat.zero_le _⟩

def tagSum (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (primary : Vector (PrimaryPool security) source.val.1.val) (body : Vector (BodyPool security) source.val.2.val) :
    CoefficientProgram order := fun output inputs centers =>
  let counts := BinaryFullResponseCounts.current security
  let result := CountedBoundedRootTags.sum counts.body order (fun tag =>
    let value := tagged security bits order data queue source sourcePrimary sourceBody primary body tag output inputs centers
    ⟨value.value,value.work+1⟩)
  ⟨result.data,counts.work+result.work+2⟩

def selected (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (primary : Vector (PrimaryPool security) source.val.1.val) (body : Vector (BodyPool security) source.val.2.val) : CoefficientProgram order :=
  BinaryCoefficientOperations.add order
    (tagged security bits order data queue source sourcePrimary sourceBody primary body (emptyTag security order))
    (tagSum security bits order data queue source sourcePrimary sourceBody primary body)

def choiceAverage (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) :
    CoefficientProgram order := fun output inputs centers =>
  let result := BinaryControlChoiceAverage.current security order source (fun primary body =>
    let value := selected security bits order data queue source sourcePrimary sourceBody primary body output inputs centers
    ⟨value.value,value.work+1⟩)
  ⟨result.data,result.work+1⟩

def fixedQueue (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order data.groups.programs
    (BinaryBackgroundPopulation.current security bits order data.groups.programs queue)
    (choiceAverage security bits order data queue source sourcePrimary sourceBody)

def response (security bits order : ℕ) (data : Data order) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) : CoefficientProgram order :=
  BinaryCoefficientScalarAverage.current security bits order (fun queue => fixedQueue security bits order data queue source sourcePrimary sourceBody)

def current (security bits order : ℕ) (data : Data order) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) :
    CoefficientProgram order := fun output inputs centers =>
  let value := response security bits order data source sourcePrimary sourceBody output inputs centers
  let basis := BinaryFullResponseData.basis security bits order data source sourcePrimary sourceBody output inputs centers
  let result := difference value.value basis.value
  ⟨result.data,value.work+basis.work+result.work+3⟩

end CurrentAFT.BinaryFullResponseProgram

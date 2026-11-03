import CurrentAFT.BinaryFullResponseProgram
import CurrentAFT.BinaryRootMetadataResources

/-! # Complete polynomial resources of the actual full-response algorithm -/
namespace CurrentAFT.BinaryFullResponseResources
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct BinaryFullResponseProgram
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryFullResponseCounts.current
  BinaryPackedRootUniform.current BinaryBackgroundPopulation.current

def taggedHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryPackedRootUniform.heightPolynomial order order data.groups data.points precision queueBits
def taggedWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryFullResponseCounts.workPolynomial+Polynomial.C (order*(2*order+4)+2)+BinaryRootMetadataSerializer.workPolynomial order+
    BinaryPackedRootUniform.workPolynomial order order data.groups data.points precision queueBits+4
def tagSumHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  CountedBoundedRootTags.heightPolynomial order BinaryProposalMetadata.sizePolynomial (taggedHeight order data precision queueBits)
def tagSumWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryFullResponseCounts.workPolynomial+CountedBoundedRootTags.workPolynomial order BinaryProposalMetadata.sizePolynomial
    (taggedHeight order data precision queueBits) (taggedWork order data precision queueBits+1)+2
def selectedHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryCoefficientOperations.addHeight (taggedHeight order data precision queueBits) (tagSumHeight order data precision queueBits)
def selectedWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryCoefficientOperations.addWork (taggedHeight order data precision queueBits) (tagSumHeight order data precision queueBits)
    (taggedWork order data precision queueBits) (tagSumWork order data precision queueBits)
def choiceHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryControlChoiceAverage.heightPolynomial order (selectedHeight order data precision queueBits)
def choiceWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryControlChoiceAverage.workPolynomial order (selectedHeight order data precision queueBits) (selectedWork order data precision queueBits+1)+1
def fixedQueueHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryFamilyArithmetic.heightPolynomial order data.groups.programs
    (BinaryBackgroundPopulation.heightPolynomial order data.groups.programs precision queueBits+choiceHeight order data precision queueBits)
def fixedQueueWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryFamilyArithmetic.workPolynomial order data.groups.programs
    (BinaryBackgroundPopulation.heightPolynomial order data.groups.programs precision queueBits+choiceHeight order data precision queueBits)
    (BinaryBackgroundPopulation.workPolynomial order data.groups.programs precision queueBits+choiceWork order data precision queueBits)
def responseHeight (order : ℕ) (data : Data order) (precision : Polynomial ℕ) :=
  BinaryCoefficientScalarAverage.heightPolynomial precision
    (fixedQueueHeight order data precision BinaryCoefficientScalarAverage.scalarBitsPolynomial)
def responseWork (order : ℕ) (data : Data order) (precision : Polynomial ℕ) :=
  BinaryCoefficientScalarAverage.workPolynomial precision
    (fixedQueueHeight order data precision BinaryCoefficientScalarAverage.scalarBitsPolynomial)
    (fixedQueueWork order data precision BinaryCoefficientScalarAverage.scalarBitsPolynomial)
def heightPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) :=
  responseHeight order data precision+BinaryFullResponseData.basisHeightPolynomial order data precision+1
def workPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) :=
  responseWork order data precision+BinaryFullResponseData.basisWorkPolynomial order data precision+
    2*primitiveWorkPolynomial (responseHeight order data precision+BinaryFullResponseData.basisHeightPolynomial order data precision)+5

theorem tagged_bounds (security order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (primary : Vector (PrimaryPool security) source.val.1.val) (body : Vector (BodyPool security) source.val.2.val)
    (tag : Tag security order) (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (tagged security (precision.eval security) order data queue source sourcePrimary sourceBody primary body tag output inputs centers).value.decode
      ((taggedHeight order data precision queueBits).eval security) ∧
    (tagged security (precision.eval security) order data queue source sourcePrimary sourceBody primary body tag output inputs centers).work ≤
      (taggedWork order data precision queueBits).eval security := by
  let counts := BinaryFullResponseCounts.current security
  let stored := tag.store
  let native : Vector (Fin (BinaryRootMetadataSerializer.population counts.leg counts.ordinary counts.queue)) tag.values.length :=
    Eq.mpr (congrArg (fun count => Vector (Fin count) tag.values.length) (BinaryFullResponseCounts.body_decomposition security)) stored.value
  let metadata := BinaryRootMetadataSerializer.current primary body native
  have hk : metadata.kept ≤ order := (BinaryRootMetadataSerializer.current_kept_le primary body native).trans tag.bounded
  have hp := BinaryPackedRootUniform.current_bounds security order order data.groups data.points precision queueBits queue hq source
    metadata.data hk tag.bounded sourcePrimary sourceBody output inputs centers hi hb
  have wm := BinaryRootMetadataSerializer.current_polynomial_work security order primary body native source.property tag.bounded
  have ws : stored.work ≤ order*(2*order+4)+2 := tag.store_work
  have wc := BinaryFullResponseCounts.current_work security
  refine ⟨hp.1,?_⟩
  change counts.work+stored.work+metadata.work+(BinaryPackedRootUniform.current _ _ _ _ _ _ _ _ _ _ _ _ _).work+4 ≤ _
  simp only [taggedWork,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_ofNat]
  change counts.work ≤ _ at wc
  dsimp only [counts,stored,native,metadata] at hp wm ws wc ⊢
  omega

theorem tagSum_bounds (security order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (primary : Vector (PrimaryPool security) source.val.1.val) (body : Vector (BodyPool security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (tagSum security (precision.eval security) order data queue source sourcePrimary sourceBody primary body output inputs centers).value.decode
      ((tagSumHeight order data precision queueBits).eval security) ∧
    (tagSum security (precision.eval security) order data queue source sourcePrimary sourceBody primary body output inputs centers).work ≤
      (tagSumWork order data precision queueBits).eval security := by
  let kernel := fun tag : Tag security order =>
    let value := tagged security (precision.eval security) order data queue source sourcePrimary sourceBody primary body tag output inputs centers
    (⟨value.value,value.work+1⟩ : RationalResult)
  have hk (tag : Tag security order) := tagged_bounds security order data precision queueBits queue hq source sourcePrimary sourceBody primary body tag output inputs centers hi hb
  have hpop : (BinaryFullResponseCounts.current security).body ≤ BinaryProposalMetadata.sizePolynomial.eval security :=
    (BinaryFullResponseCounts.current_sizes security).2.2.2.trans_eq (BinaryProposalMetadata.sizePolynomial_eval security).symm
  have hs := CountedBoundedRootTags.sum_polynomial_bounds (BinaryFullResponseCounts.current security).body order security
    BinaryProposalMetadata.sizePolynomial (taggedHeight order data precision queueBits) (taggedWork order data precision queueBits+1)
    hpop kernel (fun tag => (hk tag).1) (fun tag => by simpa only [Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right (hk tag).2 1)
  refine ⟨hs.1,?_⟩
  have wc := BinaryFullResponseCounts.current_work security
  change (BinaryFullResponseCounts.current security).work+(CountedBoundedRootTags.sum _ _ kernel).work+2 ≤ _
  simp only [tagSumWork,Polynomial.eval_add,Polynomial.eval_ofNat]
  omega

theorem selected_bounds (security order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (primary : Vector (PrimaryPool security) source.val.1.val) (body : Vector (BodyPool security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (selected security (precision.eval security) order data queue source sourcePrimary sourceBody primary body output inputs centers).value.decode
      ((selectedHeight order data precision queueBits).eval security) ∧
    (selected security (precision.eval security) order data queue source sourcePrimary sourceBody primary body output inputs centers).work ≤
      (selectedWork order data precision queueBits).eval security :=
  BinaryCoefficientOperations.add_bounds order (BinaryFirstInverseProgram.colors security) security _ _ _ _ _ _
    (tagged_bounds security order data precision queueBits queue hq source sourcePrimary sourceBody primary body (emptyTag security order))
    (tagSum_bounds security order data precision queueBits queue hq source sourcePrimary sourceBody primary body) output inputs centers hi hb

theorem choiceAverage_bounds (security order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (choiceAverage security (precision.eval security) order data queue source sourcePrimary sourceBody output inputs centers).value.decode
      ((choiceHeight order data precision queueBits).eval security) ∧
    (choiceAverage security (precision.eval security) order data queue source sourcePrimary sourceBody output inputs centers).work ≤
      (choiceWork order data precision queueBits).eval security := by
  let kernel := fun primary body =>
    let value := selected security (precision.eval security) order data queue source sourcePrimary sourceBody primary body output inputs centers
    (⟨value.value,value.work+1⟩ : RationalResult)
  have hk primary body := selected_bounds security order data precision queueBits queue hq source sourcePrimary sourceBody primary body output inputs centers hi hb
  have h := BinaryControlChoiceAverage.current_bounds security order source (selectedHeight order data precision queueBits)
    (selectedWork order data precision queueBits+1) kernel (fun primary body => (hk primary body).1)
    (fun primary body => by simpa only [Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right (hk primary body).2 1)
  exact ⟨h.1,by simpa only [choiceAverage,choiceWork,Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right h.2 1⟩

theorem fixedQueue_bounds (security order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (fixedQueue security (precision.eval security) order data queue source sourcePrimary sourceBody output inputs centers).value.decode
      ((fixedQueueHeight order data precision queueBits).eval security) ∧
    (fixedQueue security (precision.eval security) order data queue source sourcePrimary sourceBody output inputs centers).work ≤
      (fixedQueueWork order data precision queueBits).eval security :=
  BinaryCoefficientOperations.multiply_bounds order (BinaryFirstInverseProgram.colors security) security data.groups.programs _ _ _ _ _ _
    (BinaryBackgroundPopulation.current_bounds security order data.groups.programs precision queueBits queue hq)
    (choiceAverage_bounds security order data precision queueBits queue hq source sourcePrimary sourceBody) output inputs centers hi hb

theorem response_bounds (security order : ℕ) (data : Data order) (precision : Polynomial ℕ) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (response security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers).value.decode
      ((responseHeight order data precision).eval security) ∧
    (response security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers).work ≤
      (responseWork order data precision).eval security :=
  BinaryCoefficientScalarAverage.current_bounds security order (BinaryFirstInverseProgram.colors security) precision _ _ _
    (fun queue hq => fixedQueue_bounds security order data precision BinaryCoefficientScalarAverage.scalarBitsPolynomial queue hq source sourcePrimary sourceBody)
    output inputs centers hi hb

theorem current_bounds (security order : ℕ) (data : Data order) (precision : Polynomial ℕ) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers).value.decode
      ((heightPolynomial order data precision).eval security) ∧
    (current security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers).work ≤
      (workPolynomial order data precision).eval security := by
  let value := response security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers
  let basis := BinaryFullResponseData.basis security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers
  let H := (responseHeight order data precision+BinaryFullResponseData.basisHeightPolynomial order data precision).eval security
  have hr := response_bounds security order data precision source sourcePrimary sourceBody output inputs centers hi hb
  have hb := BinaryFullResponseData.basis_bounds security order data precision source sourcePrimary sourceBody output inputs centers hi hb
  have hd := difference_work value.value basis.value H
    (hr.1.mono (by simp only [H,Polynomial.eval_add]; omega)) (hb.1.mono (by simp only [H,Polynomial.eval_add]; omega))
  constructor
  · change HeightBound (difference value.value basis.value).data.decode _
    rw [difference_value,sub_eq_add_neg]
    simpa only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_one] using hr.1.add hb.1.neg
  · change value.work+basis.work+(difference value.value basis.value).work+3 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    dsimp only [H] at hd
    simp only [Polynomial.eval_add] at hd
    dsimp only [value,basis] at hd ⊢
    omega

end
end CurrentAFT.BinaryFullResponseResources

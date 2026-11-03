import CurrentAFT.BinaryFullResponseAssembly
import CurrentAFT.BinaryRootMetadataNative

/-! # The actual full binary response equals the literal current rational response -/
namespace CurrentAFT.BinaryFullResponseProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryFullResponseCounts.current
  RationalPackedRootProgram.current RationalFullResponseProgram.selection
  BinaryProposalMetadata.counts Parameters.legCount BackgroundRates.ordinaryPool

private theorem cast_embedding_ofFn {first second count : ℕ} (same : first=second) (embedding : Fin count ↪ Fin first) :
    (fun index => Fin.cast same ((Vector.ofFn embedding).get index))=
      ((Equiv.embeddingCongr (Equiv.refl (Fin count)) (finCongr same) embedding) : Fin count → Fin second) := by
  funext index
  rw [Vector.get_ofFn]
  rfl

private theorem actualChoice_ofFn (security r s : ℕ) (choice : BinaryControlChoiceAverage.Choice security r s)
    (hp : Function.Injective (Vector.ofFn choice.1).get) (hb : Function.Injective (Vector.ofFn choice.2).get) :
    BinaryRootMetadataSerializer.actualChoice (Vector.ofFn choice.1) (Vector.ofFn choice.2) hp hb=
      BinaryControlChoiceAverage.choiceEquiv security r s choice := by
  apply Prod.ext
  · apply Function.Embedding.ext
    intro index
    exact congrFun (cast_embedding_ofFn (BinaryFullResponseCounts.current_value security).1 choice.1) index
  · apply Function.Embedding.ext
    intro index
    exact congrFun (cast_embedding_ofFn (BinaryFullResponseCounts.current_value security).2.1 choice.2) index

theorem tagged_correct (security bits order : ℕ) (data : Data order) (hdata : BinaryFullResponseData.Correct data) :
    TaggedCorrect security bits order data (BinaryRootMetadataSerializer.tagBlockEquiv security) := by
  intro queue source sourcePrimary sourceBody choice tag output inputs centers hi hb
  have hp : Function.Injective (Vector.ofFn choice.1).get := by
    intro first second he
    apply choice.1.injective
    simpa only [Vector.get_ofFn] using he
  have hbody : Function.Injective (Vector.ofFn choice.2).get := by
    intro first second he
    apply choice.2.injective
    simpa only [Vector.get_ofFn] using he
  change (BinaryPackedRootUniform.current security bits order data.groups data.points queue source
    (BinaryRootMetadataSerializer.current (Vector.ofFn choice.1) (Vector.ofFn choice.2) (BinaryRootMetadataSerializer.nativeTag tag)).data
    sourcePrimary sourceBody output inputs centers).value.decode=_
  rw [BinaryPackedRootUniform.current_value security bits order data.groups hdata.1 data.points hdata.2.1 hdata.2.2
    queue source _ sourcePrimary sourceBody output inputs centers hi hb]
  rw [BinaryRootMetadataSerializer.current_rational_native bits order queue.decode (Vector.ofFn choice.1) (Vector.ofFn choice.2) hp hbody tag]
  rw [actualChoice_ofFn security source.val.1.val source.val.2.val choice hp hbody]
  rfl

theorem current_value (security bits order : ℕ) (data : Data order) (hdata : BinaryFullResponseData.Correct data)
    (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current security bits order data source sourcePrimary sourceBody output inputs centers).value.decode=
      RationalFullResponseProgram.defect security bits order source
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get :=
  current_value_of_tagged security bits order data hdata (BinaryRootMetadataSerializer.tagBlockEquiv security)
    (tagged_correct security bits order data hdata) source sourcePrimary sourceBody output inputs centers hi hb

theorem response_value (security bits order : ℕ) (data : Data order) (hdata : BinaryFullResponseData.Correct data)
    (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (response security bits order data source sourcePrimary sourceBody output inputs centers).value.decode=
      RationalFullResponseProgram.response security bits order source.val.1.val source.val.2.val
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get :=
  response_value_of_tagged security bits order data hdata (BinaryRootMetadataSerializer.tagBlockEquiv security)
    (tagged_correct security bits order data hdata) source sourcePrimary sourceBody output inputs centers hi hb

end
end CurrentAFT.BinaryFullResponseProgram

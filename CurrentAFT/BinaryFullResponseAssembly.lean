import CurrentAFT.BinaryFullResponseProgram

/-! # Exact outer algebra of the actual full response

The only local semantic bridge used here is the independently verified
selection/tag serialization. No response error or runtime estimate is
assumed by this finite-sum algebra.
-/
namespace CurrentAFT.BinaryFullResponseProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct ActualBlockFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryFullResponseCounts.current
  Parameters.bodySize Parameters.legCount BackgroundRates.ordinaryPool
  RationalFullResponseProgram.selected RationalFullResponseProgram.selection

def TaggedCorrect (security bits order : ℕ) (data : Data order)
    (numbering : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security) : Prop :=
  ∀ (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (choice : BinaryControlChoiceAverage.Choice security source.val.1.val source.val.2.val) (tag : Tag security order)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val),
    (∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) → (∀ i, centers.get i<BinaryFirstInverseProgram.colors security) →
    (tagged security bits order data queue source sourcePrimary sourceBody (Vector.ofFn choice.1) (Vector.ofFn choice.2) tag output inputs centers).value.decode=
      RationalPackedRootProgram.current security bits order queue.decode
        (RationalPackedRootProgram.actualMetadata
          (RationalFullResponseProgram.selection security _ _ (BinaryControlChoiceAverage.choiceEquiv security _ _ choice))
          (numbering.finsetCongr tag.set))
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get

theorem tagSum_value_of_tagged (security bits order : ℕ) (data : Data order)
    (numbering : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security) (hvalue : TaggedCorrect security bits order data numbering)
    (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (choice : BinaryControlChoiceAverage.Choice security source.val.1.val source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (tagSum security bits order data queue source sourcePrimary sourceBody (Vector.ofFn choice.1) (Vector.ofFn choice.2) output inputs centers).value.decode=
      ∑ tagged∈RationalFullResponseProgram.tags security order,
        RationalPackedRootProgram.current security bits order queue.decode
          (RationalPackedRootProgram.actualMetadata
            (RationalFullResponseProgram.selection security _ _ (BinaryControlChoiceAverage.choiceEquiv security _ _ choice)) tagged)
          (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get := by
  change (CountedBoundedRootTags.sum _ _ _).data.decode=_
  exact CountedBoundedRootTags.sum_value_equiv _ order numbering _ _
    (fun tag => hvalue queue source sourcePrimary sourceBody choice tag output inputs centers hi hb)

theorem selected_value_of_tagged (security bits order : ℕ) (data : Data order)
    (numbering : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security) (hvalue : TaggedCorrect security bits order data numbering)
    (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (choice : BinaryControlChoiceAverage.Choice security source.val.1.val source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (selected security bits order data queue source sourcePrimary sourceBody (Vector.ofFn choice.1) (Vector.ofFn choice.2) output inputs centers).value.decode=
      RationalFullResponseProgram.selected bits order queue.decode
        (RationalFullResponseProgram.selection security _ _ (BinaryControlChoiceAverage.choiceEquiv security _ _ choice))
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get := by
  rw [selected,BinaryCoefficientOperations.add_value,hvalue queue source sourcePrimary sourceBody choice (emptyTag security order) output inputs centers hi hb,
    tagSum_value_of_tagged security bits order data numbering hvalue queue source sourcePrimary sourceBody choice output inputs centers hi hb]
  simp only [emptyTag,CountedBoundedRootTags.Tag.set,List.toFinset_nil,Equiv.finsetCongr_apply,Finset.map_empty,RationalFullResponseProgram.selected]

private theorem finite_sum_irrel {Index : Type*} (first second : Fintype Index) (value : Index → ℚ) :
    @Finset.sum Index ℚ _ (@Finset.univ Index first) value=
      @Finset.sum Index ℚ _ (@Finset.univ Index second) value := by
  cases Subsingleton.elim first second
  rfl

private theorem choiceAverage_eq_sum (security bits order r s : ℕ) (queue : ℤ)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) (output : TruncatedArity order)
    (inputs : Fin output.val.1.val → ℕ) (centers : Fin output.val.2.val → ℕ) :
    RationalFullResponseProgram.choiceAverage security bits order r s queue sourcePrimary sourceBody output inputs centers=
      (∑ choice : UniformTaggedOutput.Choice security r s,
        RationalFullResponseProgram.selected bits order queue (RationalFullResponseProgram.selection security r s choice)
          sourcePrimary sourceBody output inputs centers)/
        (((Parameters.legCount security).descFactorial r:ℚ)*((BackgroundRates.ordinaryPool security).descFactorial s:ℚ)) := by
  have hprimary : CyclePatternProgram.selectionFintype (Parameters.legCount security) r=
      (inferInstance : Fintype (Fin r ↪ Fin (Parameters.legCount security))) := Subsingleton.elim _ _
  have hbody : CyclePatternProgram.selectionFintype (BackgroundRates.ordinaryPool security) s=
      (inferInstance : Fintype (Fin s ↪ Fin (BackgroundRates.ordinaryPool security))) := Subsingleton.elim _ _
  unfold RationalFullResponseProgram.choiceAverage
  rw [hprimary,hbody]


theorem choiceAverage_value_of_tagged (security bits order : ℕ) (data : Data order)
    (numbering : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security) (hvalue : TaggedCorrect security bits order data numbering)
    (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (choiceAverage security bits order data queue source sourcePrimary sourceBody output inputs centers).value.decode=
      RationalFullResponseProgram.choiceAverage security bits order source.val.1.val source.val.2.val queue.decode
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get := by
  change (BinaryControlChoiceAverage.current _ _ _ _).data.decode=_
  let kernel := fun primary body =>
    let value := selected security bits order data queue source sourcePrimary sourceBody primary body output inputs centers
    (⟨value.value,value.work+1⟩ : RationalResult)
  have h := BinaryControlChoiceAverage.current_value_actual security order source kernel
    (fun choice => RationalFullResponseProgram.selected bits order queue.decode
      (RationalFullResponseProgram.selection security _ _ choice)
      (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get)
    (fun choice => selected_value_of_tagged security bits order data numbering hvalue queue source sourcePrimary sourceBody choice output inputs centers hi hb)
  exact h.trans (choiceAverage_eq_sum security bits order source.val.1.val source.val.2.val queue.decode
    (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get).symm

theorem fixedQueue_value_of_tagged (security bits order : ℕ) (data : Data order) (hdata : BinaryFullResponseData.Correct data)
    (numbering : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security) (hvalue : TaggedCorrect security bits order data numbering)
    (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (fixedQueue security bits order data queue source sourcePrimary sourceBody output inputs centers).value.decode=
      RationalFullResponseProgram.fixedQueue security bits order source.val.1.val source.val.2.val queue.decode
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get :=
  BinaryFamilyValidSemantics.multiply_value order (BinaryFirstInverseProgram.colors security) data.groups.programs hdata.1.1 hdata.1.2.1 _ _ _ _
    (BinaryBackgroundPopulation.current_value security bits order data.groups.programs hdata.1.1 hdata.1.2.1 queue)
    (choiceAverage_value_of_tagged security bits order data numbering hvalue queue source sourcePrimary sourceBody) output inputs centers hi hb

theorem response_value_of_tagged (security bits order : ℕ) (data : Data order) (hdata : BinaryFullResponseData.Correct data)
    (numbering : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security) (hvalue : TaggedCorrect security bits order data numbering)
    (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (response security bits order data source sourcePrimary sourceBody output inputs centers).value.decode=
      RationalFullResponseProgram.response security bits order source.val.1.val source.val.2.val
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get :=
  BinaryFamilyValidSemantics.scalarAverage_value security bits order (BinaryFirstInverseProgram.colors security) _ _
    (fun queue => fixedQueue_value_of_tagged security bits order data hdata numbering hvalue queue source sourcePrimary sourceBody) output inputs centers hi hb

theorem current_value_of_tagged (security bits order : ℕ) (data : Data order) (hdata : BinaryFullResponseData.Correct data)
    (numbering : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security) (hvalue : TaggedCorrect security bits order data numbering)
    (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current security bits order data source sourcePrimary sourceBody output inputs centers).value.decode=
      RationalFullResponseProgram.defect security bits order source
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get := by
  simp only [current,difference_value,response_value_of_tagged security bits order data hdata numbering hvalue source sourcePrimary sourceBody output inputs centers hi hb,
    BinaryFullResponseData.basis_value security bits order data hdata source sourcePrimary sourceBody output inputs centers hi hb,
    RationalFullResponseProgram.defect,Pi.sub_apply]

end
end CurrentAFT.BinaryFullResponseProgram

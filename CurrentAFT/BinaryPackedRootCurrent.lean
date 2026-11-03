import CurrentAFT.BinaryPackedRootScalar
import CurrentAFT.BinaryRootGroupProgram
import CurrentAFT.BinaryFamilyWordProductValid
import CurrentAFT.BinaryPackedRootSum

/-! The complete packed coefficient entry: true binary role dispatch, actual
heterogeneous family products, scalar root/control factors and joint source
loops. The ideal value is the literal rational packed program. -/
namespace CurrentAFT.BinaryPackedRootCurrent
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms BinaryPackedRootMetadata
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def sourceGroup {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3)) (group : Fin groups) :
    CountedValue (Vector (Color security) 3) := storeData 3 (sourceEntry security source group)

 theorem sourceGroup_get {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3)) (group : Fin groups) (slot : Fin 3) :
    ((sourceGroup security source group).value.get slot).val = word security source group slot := by
  simp only [sourceGroup,storeData_get,sourceEntry_value,word]

 theorem sourceGroup_work {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3)) (group : Fin groups) :
    (sourceGroup security source group).work ≤ 3*(30*groups+22)+2 :=
  storeData_work _ _ _ (fun _ => sourceEntry_work security source group _)


def localFamily {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (queue : IntegerBits) (data : Data r s kept tags) (source : Vector (Color security) (((r+s)+kept)*3))
    (index : Fin ((r+s)+kept)) : CoefficientProgram order := fun arity colors centers =>
  let role := readVector RationalRootGroupProgram.LocalRole.primary data.roles index
  let input := sourceGroup security source index
  let result := BinaryRootGroupProgram.localTable security bits order programs queue role.value input.value arity colors centers
  ⟨result.value,role.work+input.work+result.work+3⟩


def localProduct {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (queue : IntegerBits) (data : Data r s kept tags) (source : Vector (Color security) (((r+s)+kept)*3)) :
    CoefficientProgram order :=
  BinaryFamilyWordProduct.product order programs.programs ((r+s)+kept) (localFamily security bits order programs queue data source)

 theorem localProduct_value {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (hprograms : BinaryRootGroupProgram.Correct programs) (queue : IntegerBits) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < (PublicParameterProgram.modulus security).count)
    (hb : ∀ i, centers.get i < (PublicParameterProgram.modulus security).count) :
    (localProduct security bits order programs queue data source arity colors centers).value.decode =
      RationalPackedRootProgram.localProduct security bits order queue.decode data.metadata (word security source) arity colors.get centers.get := by
  apply BinaryFamilyWordProduct.product_value_valid order (PublicParameterProgram.modulus security).count
    programs.programs hprograms.1 hprograms.2.1 ((r+s)+kept) _
    (fun group => RationalRootGroupProgram.localTable security bits order queue.decode (data.metadata.roles group) (word security source group))
    _ arity colors centers hc hb
  intro index arity colors centers hc hb
  change (BinaryRootGroupProgram.localTable _ _ _ _ _ _ _ _ _ _).value.decode = _
  rw [BinaryRootGroupProgram.localTable_value _ _ _ _ hprograms _ _ _ _ _ _ hc hb]
  simp only [readVector_value,Data.metadata]
  congr 1
  funext slot
  exact sourceGroup_get security source index slot


def summand {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (queue : IntegerBits) (data : Data r s kept tags)
    (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) : CoefficientProgram order := fun arity colors centers =>
  let scalar := BinaryPackedRootScalar.current security bits pointProgram data sourcePrimary sourceBody source
  let family := localProduct security bits order programs queue data source arity colors centers
  let result := RationalBits.multiply scalar.data family.value
  ⟨result.data,scalar.work+family.work+result.work+3⟩

 theorem summand_value {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (hprograms : BinaryRootGroupProgram.Correct programs) (pointProgram : BinaryWeightedPointKernel.Program r s)
    (hpoint : pointProgram.meaning RationalBits.decode = BinaryWeightedPointKernel.pointSyntax r s)
    (queue : IntegerBits) (data : Data r s kept tags) (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < (PublicParameterProgram.modulus security).count)
    (hb : ∀ i, centers.get i < (PublicParameterProgram.modulus security).count) :
    (summand security bits order programs pointProgram queue data sourcePrimary sourceBody source arity colors centers).value.decode =
      RationalPackedRootProgram.summand security bits order queue.decode data.metadata (fun index => (sourcePrimary.get index).val)
        (fun index => (sourceBody.get index).val) (word security source) arity colors.get centers.get := by
  change (RationalBits.multiply _ _).data.decode = _
  rw [RationalBits.multiply_value,BinaryPackedRootScalar.current_value _ _ _ hpoint,
    localProduct_value _ _ _ _ hprograms _ _ _ _ _ _ hc hb]
  unfold RationalPackedRootProgram.summand
  split_ifs <;> simp only [zero_mul]


def current {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (queue : IntegerBits) (data : Data r s kept tags)
    (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s) : CoefficientProgram order :=
  fun arity colors centers =>
    let result := BinaryPackedRootSum.current security ((r+s)+kept)
      (fun source =>
        let value := summand security bits order programs pointProgram queue data sourcePrimary sourceBody source arity colors centers
        (⟨value.value,value.work⟩ : RationalResult))
    ⟨result.data,result.work+1⟩

 theorem current_value {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (hprograms : BinaryRootGroupProgram.Correct programs) (pointProgram : BinaryWeightedPointKernel.Program r s)
    (hpoint : pointProgram.meaning RationalBits.decode = BinaryWeightedPointKernel.pointSyntax r s)
    (queue : IntegerBits) (data : Data r s kept tags) (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < (PublicParameterProgram.modulus security).count)
    (hb : ∀ i, centers.get i < (PublicParameterProgram.modulus security).count) :
    (current security bits order programs pointProgram queue data sourcePrimary sourceBody arity colors centers).value.decode =
      RationalPackedRootProgram.current security bits order queue.decode data.metadata (fun index => (sourcePrimary.get index).val)
        (fun index => (sourceBody.get index).val) arity colors.get centers.get := by
  change (BinaryPackedRootSum.current _ _ _).data.decode = _
  unfold RationalPackedRootProgram.current
  apply BinaryPackedRootSum.current_value security ((r+s)+kept) _
    (fun input => RationalPackedRootProgram.summand security bits order queue.decode data.metadata
      (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) input arity colors.get centers.get)
  intro source
  exact summand_value security bits order programs hprograms pointProgram hpoint queue data sourcePrimary sourceBody source arity colors centers hc hb

end CurrentAFT.BinaryPackedRootCurrent

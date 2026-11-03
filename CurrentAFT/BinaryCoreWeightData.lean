import CurrentAFT.CurrentCoreProposal
import CurrentAFT.BinaryWeightResources

/-! Materializing the two actual public control pools for weight evaluation. -/
namespace CurrentAFT.BinaryCoreWeightData
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions BinaryWeightLocal
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current Parameters.legCount Parameters.bodySize Parameters.dimension

def ordinaryEquiv (security : ℕ) : Fin (CurrentProposalDimensions.current security).ordinary ≃
    Fin (BackgroundRates.ordinaryPool security) := finCongr (current_values security).2.2.2.2.1

def color (security : ℕ) (value : FirstHistogram.Palette security) : Fin (colors security) :=
  value.cast (PublicParameterProgram.modulus_value security).symm

def primaryAddress (security : ℕ) (index : Fin (CurrentProposalDimensions.current security).legs) :
    Fin (CurrentProposalDimensions.current security).controls :=
  ⟨index.val, by
    have h := index.isLt
    have hl := (current_values security).2.1
    have hc := (current_values security).2.2.2.2.2
    omega⟩

def ordinaryAddress (security : ℕ) (index : Fin (CurrentProposalDimensions.current security).ordinary) :
    CountedValue (Fin (CurrentProposalDimensions.current security).controls) :=
  let sizes := CurrentProposalDimensions.current security
  let address := addCounter sizes.legs index.val
  ⟨⟨address.count, by
    rw [addCounter_value, (current_values security).2.1, (current_values security).2.2.2.2.2]
    have h := index.isLt
    have he := (current_values security).2.2.2.2.1
    omega⟩, sizes.work+address.work+2⟩

theorem primaryAddress_value (security : ℕ) (index : Fin (CurrentProposalDimensions.current security).legs) :
    primaryAddress security index = (controlsEquiv security).symm (.inl (legEquiv security index)) := by
  apply Fin.ext
  rfl

theorem ordinaryAddress_value (security : ℕ) (index : Fin (CurrentProposalDimensions.current security).ordinary) :
    (ordinaryAddress security index).value = (controlsEquiv security).symm (.inr (ordinaryEquiv security index)) := by
  apply Fin.ext
  simp only [ordinaryAddress, addCounter_value, (current_values security).2.1]
  rfl

def primaryEntry (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).legs) : CountedValue (Fin (colors security) × Fin (colors security)) :=
  let group := readVector (defaultControl security) data.controls (primaryAddress security index)
  ⟨(color security group.value.1, color security group.value.2.val), group.work+2⟩

def ordinaryEntry (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).ordinary) : CountedValue (Fin (colors security)) :=
  let address := ordinaryAddress security index
  let group := readVector (defaultControl security) data.controls address.value
  ⟨color security group.value.2.val, address.work+group.work+2⟩

def groups (security : ℕ) (data : MaterializedCore security) :
    CountedValue (Vector (Fin (colors security) × Fin (colors security)) (CurrentProposalDimensions.current security).legs) :=
  let sizes := CurrentProposalDimensions.current security
  let result := storeData sizes.legs (primaryEntry security data)
  ⟨result.value, sizes.work+result.work+2⟩

def centers (security : ℕ) (data : MaterializedCore security) :
    CountedValue (Vector (Fin (colors security)) (CurrentProposalDimensions.current security).ordinary) :=
  let sizes := CurrentProposalDimensions.current security
  let result := storeData sizes.ordinary (ordinaryEntry security data)
  ⟨result.value, sizes.work+result.work+2⟩

theorem groups_value (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).legs) :
    ((groups security data).value.get index).1.val = (data.core.controls (.inl (legEquiv security index))).1.val ∧
    ((groups security data).value.get index).2.val = (data.core.controls (.inl (legEquiv security index))).2.val.val := by
  simp only [groups, storeData_get, primaryEntry, readVector_value, primaryAddress_value, color,
    Fin.val_cast, MaterializedCore.core, decode, and_self]

theorem centers_value (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).ordinary) :
    ((centers security data).value.get index).val =
      (data.core.controls (.inr (ordinaryEquiv security index))).2.val.val := by
  simp only [centers, storeData_get, ordinaryEntry, readVector_value, ordinaryAddress_value, color,
    Fin.val_cast, MaterializedCore.core, decode]

theorem primaryPool_pos (security : ℕ) : 0 < (CurrentProposalDimensions.current security).legs := by
  rw [(current_values security).2.1]
  exact BinaryWeightResources.primaryPool_pos security

theorem bodyPool_pos (security : ℕ) : 0 < (CurrentProposalDimensions.current security).ordinary := by
  rw [(current_values security).2.2.2.2.1]
  exact BackgroundRates.ordinaryPool_pos security

def current (security bits order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (data : MaterializedCore security) : CountedValue RationalBits :=
  let sizes := CurrentProposalDimensions.current security
  let primary := groups security data
  let body := centers security data
  let value := BinaryWeightProgram.current security bits order sizes.legs sizes.ordinary
    (primaryPool_pos security) (bodyPool_pos security) table primary.value body.value
  ⟨value.data, sizes.work+primary.work+body.work+value.work+4⟩

noncomputable section
open scoped Classical
attribute [local irreducible] RationalWeightProgram.current

theorem current_value (security bits order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (data : MaterializedCore security) :
    (current security bits order table data).value.decode =
      RationalWeightProgram.current security bits order (CurrentProposalDimensions.current security).legs
        (CurrentProposalDimensions.current security).ordinary (rawTable security order table)
        (fun index => ((data.core.controls (.inl (legEquiv security index))).1.val,
          (data.core.controls (.inl (legEquiv security index))).2.val.val))
        (fun index => (data.core.controls (.inr (ordinaryEquiv security index))).2.val.val) := by
  simp only [current, BinaryWeightProgram.current_value, (groups_value security data _).1,
    (groups_value security data _).2, centers_value]

theorem pool_cast (security bits order primary body actualPrimary actualBody : ℕ)
    (hp : primary = actualPrimary) (hb : body = actualBody) (table : RationalWeightProgram.RawTable order)
    (groups : Fin actualPrimary → ℕ × ℕ) (centers : Fin actualBody → ℕ) :
    RationalWeightProgram.current security bits order primary body table
      (fun index => groups (index.cast hp)) (fun index => centers (index.cast hb)) =
      RationalWeightProgram.current security bits order actualPrimary actualBody table groups centers := by
  cases hp
  cases hb
  rfl

theorem current_value_actual (security bits order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (data : MaterializedCore security) :
    (current security bits order table data).value.decode =
      RationalWeightProgram.current security bits order (Parameters.legCount security)
        (BackgroundRates.ordinaryPool security) (rawTable security order table)
        (fun index => ((data.core.controls (.inl index)).1.val, (data.core.controls (.inl index)).2.val.val))
        (fun index => (data.core.controls (.inr index)).2.val.val) := by
  rw [current_value]
  have h := pool_cast security bits order (CurrentProposalDimensions.current security).legs
    (CurrentProposalDimensions.current security).ordinary (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security) (current_values security).2.1 (current_values security).2.2.2.2.1
    (rawTable security order table)
    (fun index => ((data.core.controls (.inl index)).1.val, (data.core.controls (.inl index)).2.val.val))
    (fun index => (data.core.controls (.inr index)).2.val.val)
  exact h

end
end CurrentAFT.BinaryCoreWeightData

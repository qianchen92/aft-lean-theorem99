import AFT.ActualJointFock

/-! # Exact physical output coordinates of primary and body roles -/
namespace AFT.V7Calibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev PrimaryRoles {count : ℕ} (role : Fin count → Bool) := {i : Fin count // role i=true}
abbrev BodyRoles {count : ℕ} (role : Fin count → Bool) := {i : Fin count // ¬role i=true}
abbrev RoleSources {count : ℕ} (role : Fin count → Bool) := (PrimaryRoles role ⊕ PrimaryRoles role) ⊕ BodyRoles role

def roleSourceSlots {count : ℕ} (role : Fin count → Bool) : RoleSources role → Type
  | .inl (.inl _) => Fin 3
  | .inl (.inr _) => Fin 1
  | .inr _ => Fin 1

instance roleSourceSlotsFintype {count : ℕ} (role : Fin count → Bool) (source : RoleSources role) :
    Fintype (roleSourceSlots role source) := by rcases source with ⟨_|_⟩|_ <;> dsimp [roleSourceSlots] <;> infer_instance

def rolePartition {count : ℕ} (role : Fin count → Bool) : (PrimaryRoles role ⊕ BodyRoles role) ≃ Fin count :=
  Equiv.sumCompl (fun index => role index=true)

def primaryRoleSlotEquiv {count : ℕ} (role : Fin count → Bool) (index : PrimaryRoles role) :
    actualRoleSlots (role (rolePartition role (.inl index))) ≃ Fin 4 :=
  Equiv.cast (by change actualRoleSlots (role index.val)=Fin 4; rw [index.property]; rfl)

def bodyRoleSlotEquiv {count : ℕ} (role : Fin count → Bool) (index : BodyRoles role) :
    actualRoleSlots (role (rolePartition role (.inr index))) ≃ Fin 1 :=
  Equiv.cast (by
    change actualRoleSlots (role index.val)=Fin 1
    have hh : role index.val=false := by simpa using index.property
    rw [hh]
    rfl)

/-- Four primary outputs are the attached triple followed by its compensator. -/
def primaryOutputSplit (Primary : Type*) : (Primary × Fin 4) ≃ (Primary × Fin 3) ⊕ (Primary × Fin 1) :=
  (Equiv.prodCongr (Equiv.refl Primary) (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4).symm).trans
    (Equiv.prodSumDistrib Primary (Fin 3) (Fin 1))

def roleOutputPartition {count : ℕ} (role : Fin count → Bool) :
    (Sigma (fun index => actualRoleSlots (role index))) ≃
      (PrimaryRoles role × Fin 4) ⊕ (BodyRoles role × Fin 1) :=
  ((Equiv.sigmaCongrLeft (β:=fun index => actualRoleSlots (role index)) (rolePartition role)).symm.trans
    (Equiv.sumSigmaDistrib (fun index => actualRoleSlots (role (rolePartition role index))))).trans
      (Equiv.sumCongr (Equiv.sigmaEquivProdOfEquiv (primaryRoleSlotEquiv role))
        (Equiv.sigmaEquivProdOfEquiv (bodyRoleSlotEquiv role)))

def sourceOutputPartition {count : ℕ} (role : Fin count → Bool) :
    Sigma (roleSourceSlots role) ≃
      ((PrimaryRoles role × Fin 3) ⊕ (PrimaryRoles role × Fin 1)) ⊕ (BodyRoles role × Fin 1) :=
  (Equiv.sumSigmaDistrib (roleSourceSlots role)).trans
    (Equiv.sumCongr ((Equiv.sumSigmaDistrib (fun index => roleSourceSlots role (.inl index))).trans
      (Equiv.sumCongr (Equiv.sigmaEquivProd _ _) (Equiv.sigmaEquivProd _ _)))
      (Equiv.sigmaEquivProd _ _))

def roleOutputSourceEquiv {count : ℕ} (role : Fin count → Bool) :
    (Sigma (fun index => actualRoleSlots (role index))) ≃ Sigma (roleSourceSlots role) :=
  ((roleOutputPartition role).trans (Equiv.sumCongr (primaryOutputSplit (PrimaryRoles role))
    (Equiv.refl _))).trans (sourceOutputPartition role).symm


@[simp] theorem roleOutputSourceEquiv_symm_attached {count : ℕ} (role : Fin count → Bool)
    (index : PrimaryRoles role) (slot : Fin 3) :
    (roleOutputSourceEquiv role).symm ⟨.inl (.inl index),slot⟩=
      ⟨index.val,(primaryRoleSlotEquiv role index).symm (Fin.castAdd 1 slot)⟩ := by rfl

@[simp] theorem roleOutputSourceEquiv_symm_compensator {count : ℕ} (role : Fin count → Bool)
    (index : PrimaryRoles role) (slot : Fin 1) :
    (roleOutputSourceEquiv role).symm ⟨.inl (.inr index),slot⟩=
      ⟨index.val,(primaryRoleSlotEquiv role index).symm (Fin.natAdd 3 slot)⟩ := by rfl

@[simp] theorem roleOutputSourceEquiv_symm_body {count : ℕ} (role : Fin count → Bool)
    (index : BodyRoles role) (slot : Fin 1) :
    (roleOutputSourceEquiv role).symm ⟨.inr index,slot⟩=
      ⟨index.val,(bodyRoleSlotEquiv role index).symm slot⟩ := by rfl

end
end AFT.V7Calibration

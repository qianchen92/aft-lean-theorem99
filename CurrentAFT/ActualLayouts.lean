import CurrentAFT.ActualBlockFock
import CurrentAFT.CycleRootExpansion
import CurrentAFT.ConditionalHistogramMean

/-! # The exact rotation between physical block and body-role indices -/
namespace CurrentAFT.ActualLayouts
open ActualBlockFock ConditionalHistogramMean
noncomputable section

def blockRoleEquiv (security : ℕ) : BlockIndex security ≃ RoleIndex security :=
  (Equiv.sumComm _ _).trans (Equiv.sumAssoc _ _ _)

@[simp] theorem blockRole_primary (security : ℕ) (index : Fin (Parameters.legCount security)) :
    blockRoleEquiv security (.inl index) = .inr (.inr index) := rfl

@[simp] theorem blockRole_center (security : ℕ) (index : Fin (centerCount security)) :
    blockRoleEquiv security (.inr (.inl index)) = .inl index := rfl

@[simp] theorem blockRole_queue (security : ℕ) (index : Fin (Parameters.modulus security)) :
    blockRoleEquiv security (.inr (.inr index)) = .inr (.inl index) := rfl

def blockLayout {security : ℕ} (layout : RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security) :
    BlockIndex security ≃ CycleRootExpansion.Vertex security := (blockRoleEquiv security).trans layout

@[simp] theorem blockLayout_primary {security : ℕ}
    (layout : RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security) (index : Fin (Parameters.legCount security)) :
    blockLayout layout (.inl index) = layout (.inr (.inr index)) := rfl

@[simp] theorem blockLayout_center {security : ℕ}
    (layout : RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security) (index : Fin (centerCount security)) :
    blockLayout layout (.inr (.inl index)) = layout (.inl index) := rfl

@[simp] theorem blockLayout_queue {security : ℕ}
    (layout : RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security) (index : Fin (Parameters.modulus security)) :
    blockLayout layout (.inr (.inr index)) = layout (.inr (.inl index)) := rfl

end
end CurrentAFT.ActualLayouts

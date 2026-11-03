import CurrentAFT.PublicCoefficientOutput
import CurrentAFT.PublicCharge

/-! # The natural body and two-leg endpoints are the actual physical slots -/
namespace CurrentAFT.PublicEndpointPlacement
open AFT ActualBlockFock ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean PublicCoefficientOutput
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev AssemblyIndex (security : ℕ) :=
  PublicCharge.EndpointIndex (Parameters.bodySize security) (Fin (Parameters.legCount security))

def toPhysical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    AssemblyIndex security → Sigma (Slots security)
  | .inl vertex => match layout.symm vertex with
    | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
    | .inr (.inl point) => ⟨.inr (.inr point), (0 : Fin 1)⟩
    | .inr (.inr leg) => ⟨.inl leg, (2 : Fin 3)⟩
  | .inr (.inl leg) => ⟨.inl leg, (0 : Fin 3)⟩
  | .inr (.inr leg) => ⟨.inl leg, (1 : Fin 3)⟩

def toAssembly (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Sigma (Slots security) → AssemblyIndex security
  | ⟨.inl leg, slot⟩ => Fin.cases (.inr (.inl leg))
      (fun slot => Fin.cases (.inr (.inr leg)) (fun _ => .inl (layout (.inr (.inr leg)))) slot) slot
  | ⟨.inr (.inl center), _⟩ => .inl (layout (.inl center))
  | ⟨.inr (.inr point), _⟩ => .inl (layout (.inr (.inl point)))

theorem toAssembly_toPhysical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (index : AssemblyIndex security) : toAssembly security layout (toPhysical security layout index) = index := by
  rcases index with vertex | (leg | leg)
  · change toAssembly security layout (match layout.symm vertex with
      | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
      | .inr (.inl point) => ⟨.inr (.inr point), (0 : Fin 1)⟩
      | .inr (.inr leg) => ⟨.inl leg, (2 : Fin 3)⟩) = .inl vertex
    generalize hrole : layout.symm vertex = role
    have hvertex : layout role = vertex := by rw [← hrole, Equiv.apply_symm_apply]
    rcases role with center | (point | attached)
    · exact congrArg Sum.inl hvertex
    · exact congrArg Sum.inl hvertex
    · exact congrArg Sum.inl hvertex
  · rfl
  · rfl

theorem toPhysical_toAssembly (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (index : Sigma (Slots security)) : toPhysical security layout (toAssembly security layout index) = index := by
  rcases index with ⟨leg | (center | point), slot⟩
  · change Fin 3 at slot
    fin_cases slot
    · rfl
    · rfl
    · change ((match layout.symm (layout (.inr (.inr leg))) with
        | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
        | .inr (.inl point) => ⟨.inr (.inr point), (0 : Fin 1)⟩
        | .inr (.inr leg) => ⟨.inl leg, (2 : Fin 3)⟩) : Sigma (Slots security)) = _
      rw [Equiv.symm_apply_apply]
      rfl
  · change Fin 1 at slot
    have hslot : slot = (0 : Fin 1) := Subsingleton.elim _ _
    subst slot
    simp only [toAssembly, toPhysical, Equiv.symm_apply_apply]
  · change Fin 1 at slot
    have hslot : slot = (0 : Fin 1) := Subsingleton.elim _ _
    subst slot
    simp only [toAssembly, toPhysical, Equiv.symm_apply_apply]

def endpointEquiv (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    AssemblyIndex security ≃ Sigma (Slots security) where
  toFun := toPhysical security layout
  invFun := toAssembly security layout
  left_inv := toAssembly_toPhysical security layout
  right_inv := toPhysical_toAssembly security layout

def endpointFlatten (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    AssemblyIndex security ≃ Fin (Parameters.dimension security) :=
  (endpointEquiv security layout).trans (flatten security)

theorem sum_flatten {Group : Type*} [AddCommMonoid Group] (security : ℕ)
    (layout : RoleIndex security ≃ BodyIndex security) (word : AssemblyIndex security → Group) :
    (∑ index, word ((endpointFlatten security layout).symm index)) = ∑ index, word index :=
  (endpointFlatten security layout).symm.sum_comp word

end
end CurrentAFT.PublicEndpointPlacement

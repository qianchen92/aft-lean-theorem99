import CurrentAFT.CurrentAffineEmissionBridge
import CurrentAFT.LobsterAffineLoad

/-! The actual linear load in the explicitly numbered physical slots. -/
namespace CurrentAFT.CurrentLinearPhysicalLoad
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentAffineEmissionBridge PublicEndpointPlacement
  LobsterCoordinates LobsterMixerMatrix PublicCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev sourceEdges (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :=
  edgeCoordinates ℤ (bodyEdges security) (Parameters.legCount security) (splitSource security input).1

def path (security : ℕ) (core : Core security) (input : Fin (Parameters.dimension security) → ℤ)
    (vertex : BodyIndex security) : ℤ :=
  pathLoad (bodyEdges security) (sourceEdges security input).1
    (CurrentAffineGeometry.bodyEquiv security (core.bodyPermutation.symm vertex))

def primary (security : ℕ) (scale shear : Fin (Parameters.legCount security) → ℤ)
    (input : Fin (Parameters.dimension security) → ℤ) (leg : Fin (Parameters.legCount security)) : ℤ :=
  scale leg * (sourceEdges security input).2.1 leg + shear leg * (sourceEdges security input).2.2 leg

def physical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ) :
    Sigma (Slots security) → ℤ
  | ⟨.inl leg, slot⟩ => ![primary security scale shear input leg,
      -primary security scale shear input leg - (sourceEdges security input).2.2 leg,
      path security core input (layout (.inr (.inr leg))) + (sourceEdges security input).2.2 leg] slot
  | ⟨.inr (.inl center), _⟩ => path security core input (layout (.inl center))
  | ⟨.inr (.inr queue), _⟩ => path security core input (layout (.inr (.inl queue))) + (splitSource security input).2

theorem at_natural (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ)
    (vertex : AssemblyIndex security) :
    linearLoad security layout core scale shear input
        (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
      LobsterIncidence.load (placement security core) (attachments security layout)
        ((sourceEdges security input).1, (primary security scale shear input, (sourceEdges security input).2.2))
        (Sum.map (CurrentAffineGeometry.bodyEquiv security) id vertex) +
      (splitSource security input).2 * AffineRealization.queueColumn (bodyEdges security) (Parameters.legCount security)
        (Parameters.modulus security) (queues security layout) (relabeling security layout core)
        (relabeling security layout core (naturalNumbering security vertex)) := by
  have hi : (dimensionEquiv security).symm
      (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
      relabeling security layout core (naturalNumbering security vertex) := by
    apply (dimensionEquiv security).injective
    rw [Equiv.apply_symm_apply, relabeling_natural]
  unfold linearLoad
  rw [hi]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, relabeledBasis_apply,
    Equiv.symm_apply_apply]
  rw [LobsterAffineLoad.mixed_coordinates]
  simp only [naturalNumbering, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply]
  rfl

theorem at_physical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ)
    (point : Sigma (Slots security)) :
    linearLoad security layout core scale shear input
      (core.endpointPermutation.symm (CurrentPhysicalNumbering.numbering security point)) =
      physical security layout core scale shear input point := by
  have hp : CurrentPhysicalNumbering.numbering security point =
      endpointFlatten security layout (toAssembly security layout point) := by
    change PublicCoefficientOutput.flatten security point =
      PublicCoefficientOutput.flatten security (toPhysical security layout (toAssembly security layout point))
    rw [toPhysical_toAssembly]
  rw [hp, at_natural]
  rcases point with ⟨leg | (center | queue), slot⟩
  · change Fin 3 at slot
    fin_cases slot <;>
      simp [toAssembly, Fin.cases, Fin.induction, Fin.induction.go, naturalNumbering, LobsterAffineLoad.queueColumn_leg,
        LobsterAffineLoad.queueColumn_body, LobsterIncidence.load, attachmentIncrement,
        attachments, attachmentPosition, queues, queuePosition, physical, path, placement]
  · simp [toAssembly, naturalNumbering, LobsterAffineLoad.queueColumn_body,
      LobsterIncidence.load, attachmentIncrement, attachments, attachmentPosition,
      queues, queuePosition, physical, path, placement]
  · simp [toAssembly, naturalNumbering, LobsterAffineLoad.queueColumn_body,
      LobsterIncidence.load, attachmentIncrement, attachments, attachmentPosition,
      queues, queuePosition, physical, path, placement]

end
end CurrentAFT.CurrentLinearPhysicalLoad

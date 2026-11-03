import CurrentAFT.CurrentBinaryOffsetLoad
import CurrentAFT.CurrentLinearPhysicalLoad

/-! Exact current semantics of the executed integral load arrays. -/
namespace CurrentAFT.CurrentBinaryLoadSemantic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentBinaryLoadColumns CurrentEmissionMetadata
open CurrentCoreProposal (MaterializedCore)
open
  CurrentLinearPhysicalLoad CurrentAffineGeometry CurrentAffineLoad
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentEmissionMetadata.current CurrentProposalDimensions.current

def blockEquiv (security : ℕ) : (Fin (Legs security) ⊕ Fin (current security).rest) ≃ BlockIndex security :=
  Equiv.sumCongr (CurrentEmissionMetadata.legEquiv security)
    ((restEquiv security).trans finSumFinEquiv.symm)

theorem root_address (security : ℕ) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    (blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1 =
      CurrentEmissionRootOrder.rootNumbering security (blockEquiv security point) := by
  rcases point with leg | body
  · apply Fin.ext
    rfl
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    all_goals
      apply Fin.ext
      simp only [blockEquiv, Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply,
        ← he, Equiv.symm_apply_apply]
    · change (Legs security)+body.val=Parameters.legCount security+center.val
      have hv := congrArg Fin.val he
      change center.val=body.val at hv
      rw [show Legs security=Parameters.legCount security from (CurrentProposalDimensions.current_values security).2.1, hv]
    · change (Legs security)+body.val=Parameters.legCount security+(centerCount security+queue.val)
      have hv := congrArg Fin.val he
      change centerCount security+queue.val=body.val at hv
      rw [show Legs security=Parameters.legCount security from (CurrentProposalDimensions.current_values security).2.1, hv]

theorem block_role (security : ℕ) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    CurrentEmissionRootOrder.rootToRole security (blockEquiv security point) = CurrentBinaryBaselines.role security point := by
  rcases point with leg | body
  · rfl
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    all_goals simp only [blockEquiv, CurrentBinaryBaselines.role, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.trans_apply, ← he, Equiv.symm_apply_apply]; rfl

theorem root_position_value (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    ((CurrentEmissionRootOrder.positions security layout core).value.get
      ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1)).val =
      (core.core.bodyPermutation.symm (layout.layout (CurrentBinaryBaselines.role security point))).val := by
  have h := CurrentEmissionRootOrder.positions_actual security layout core
    ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1)
  rw [root_address, Equiv.symm_apply_apply, block_role] at h
  have hv := congrArg (fun vertex : BodyIndex security => vertex.val) h
  simpa only [CurrentProposalDimensions.bodyEquiv, finCongr_apply, Fin.val_cast, root_address] using hv

def basisInput (security : ℕ) (column : Fin ((current security).edges+1)) : Fin (Parameters.dimension security) → ℤ :=
  Pi.single (vertexEquiv security column) 1

theorem basis_value (security : ℕ) (column : Fin ((current security).edges+1)) (index : Fin (Parameters.dimension security)) :
    (basisInput security column) index = if index.val=column.val then 1 else 0 := by
  simp only [basisInput, Pi.single_apply, Fin.ext_iff]
  rfl

theorem body_basis (security : ℕ) (column : Fin ((current security).edges+1)) :
    (sourceEdges security (basisInput security column)).1 =
      fun edge => if edge.val=column.val then 1 else 0 := by
  funext edge
  change (basisInput security column)
    (coordinateNumbering security (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inl edge)))) = _
  rw [basis_value]
  rfl

theorem first_basis (security : ℕ) (column : Fin ((current security).edges+1)) (leg : Fin (Parameters.legCount security)) :
    (sourceEdges security (basisInput security column)).2.1 leg =
      if bodyEdges security+leg.val=column.val then 1 else 0 := by
  change (basisInput security column)
    (coordinateNumbering security (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inr (.inl leg))))) = _
  rw [basis_value]
  rfl

theorem second_basis (security : ℕ) (column : Fin ((current security).edges+1)) (leg : Fin (Parameters.legCount security)) :
    (sourceEdges security (basisInput security column)).2.2 leg =
      if bodyEdges security+(Parameters.legCount security+leg.val)=column.val then 1 else 0 := by
  change (basisInput security column)
    (coordinateNumbering security (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inr (.inr leg))))) = _
  rw [basis_value]
  rfl

theorem queue_basis (security : ℕ) (column : Fin ((current security).edges+1)) :
    (splitSource security (basisInput security column)).2 =
      if column.val=(current security).edges then 1 else 0 := by
  change (basisInput security column) (coordinateNumbering security (.inr ())) = _
  rw [basis_value]
  change (if edgeCount security=column.val then (1 : ℤ) else 0)=_
  simp only [(current_values security).2.1, eq_comm]

theorem primary_basis (security : ℕ) (column : Fin ((current security).edges+1))
    (scale shear : Fin (Legs security) → ℤ) (leg : Fin (Legs security)) :
    primary security (fun i => scale ((CurrentEmissionMetadata.legEquiv security).symm i))
      (fun i => shear ((CurrentEmissionMetadata.legEquiv security).symm i))
      (basisInput security column) (CurrentEmissionMetadata.legEquiv security leg) =
      primaryEntry security column.val scale shear leg := by
  rw [primary, first_basis, second_basis]
  simp only [Equiv.symm_apply_apply]
  have hleg : (CurrentEmissionMetadata.legEquiv security leg).val=leg.val := rfl
  rw [hleg]
  unfold primaryEntry
  simp only [(current_values security).1, show Legs security=Parameters.legCount security from
    (CurrentProposalDimensions.current_values security).2.1]
  simp only [bodyEdges, add_comm (Parameters.legCount security) leg.val, ← add_assoc,
    eq_comm, mul_ite, mul_one, mul_zero]

theorem second_basis_native (security : ℕ) (column : Fin ((current security).edges+1)) (leg : Fin (Legs security)) :
    (sourceEdges security (basisInput security column)).2.2 (CurrentEmissionMetadata.legEquiv security leg) =
      secondEntry security column.val leg := by
  rw [second_basis]
  unfold secondEntry
  simp only [(current_values security).1, show Legs security=Parameters.legCount security from
    (CurrentProposalDimensions.current_values security).2.1]
  have hleg : (CurrentEmissionMetadata.legEquiv security leg).val=leg.val := rfl
  rw [hleg]
  simp only [bodyEdges, add_comm (Parameters.legCount security) leg.val, ← add_assoc, eq_comm]

theorem path_basis (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (column : Fin ((current security).edges+1)) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    pathValue security column.val (CurrentEmissionRootOrder.positions security layout core).value point =
      path security core.core (basisInput security column)
        (layout.layout (CurrentBinaryBaselines.role security point)) := by
  unfold path pathValue
  rw [body_basis, CurrentPathImpulse.pathLoad_indicator, CurrentPathImpulse.pathLoad_indicator]
  simp only [Fin.val_cast]
  simp only [root_position_value, (current_values security).1]
  rfl

theorem loadEntry_eq (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (column : Fin ((current security).edges+1)) (scale shear : Fin (Legs security) → ℤ) (point : Point security) :
    loadEntry security column.val scale shear (CurrentEmissionRootOrder.positions security layout core).value point =
      CurrentAffineEmissionBridge.linearLoad security layout.layout core.core
        (fun leg => scale ((CurrentEmissionMetadata.legEquiv security).symm leg))
        (fun leg => shear ((CurrentEmissionMetadata.legEquiv security).symm leg))
        (basisInput security column)
        (core.core.endpointPermutation.symm (CurrentPhysicalNumbering.numbering security (pointEquiv security point))) := by
  rw [at_physical]
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    fin_cases slot <;> simp only [pointEquiv, Equiv.coe_fn_mk, physical, loadEntry, Matrix.cons_val_zero', Matrix.cons_val_succ',
      primary_basis, second_basis_native, path_basis, CurrentBinaryBaselines.role]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    · have hv := congrArg Fin.val he
      change center.val=body.val at hv
      have hn : ¬(current security).centers ≤ body.val := by
        rw [(current_values security).2.2.2, ← hv]
        exact Nat.not_le.mpr center.isLt
      simp only [pointEquiv, Equiv.coe_fn_mk, loadEntry, physical, ← he, Equiv.symm_apply_apply, path_basis,
        CurrentBinaryBaselines.role, hn, false_and, if_false, add_zero]
    · have hv := congrArg Fin.val he
      change centerCount security+queue.val=body.val at hv
      have hy : (current security).centers ≤ body.val := by
        rw [(current_values security).2.2.2, ← hv]
        omega
      simp only [pointEquiv, Equiv.coe_fn_mk, loadEntry, physical, ← he, Equiv.symm_apply_apply, path_basis,
        CurrentBinaryBaselines.role, hy, true_and, queue_basis]

end
end CurrentAFT.CurrentBinaryLoadSemantic

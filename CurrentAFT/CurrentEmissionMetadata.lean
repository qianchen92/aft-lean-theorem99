import CurrentAFT.CurrentEmissionRootOrder
import CurrentAFT.CurrentPhysicalNumbering
import AFT.BinaryPhysicalBaseline

/-! Executed counters and explicit physical coordinates of the current affine emitter. -/
namespace CurrentAFT.CurrentEmissionMetadata
open AFT AFT.BinaryArithmetic CurrentProposalDimensions CurrentProposalResources
open ActualBlockFock
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount Parameters.dimension
  subtractCounter

structure Result where
  bodyEdges : ℕ
  edges : ℕ
  rest : ℕ
  centers : ℕ
  work : ℕ


def current (security : ℕ) : Result :=
  let dimensions := CurrentProposalDimensions.current security
  let bodyEdges := subtractCounter dimensions.body 1
  let edges := subtractCounter dimensions.dimension 1
  let rest := subtractCounter dimensions.body dimensions.legs
  let centers := subtractCounter rest.count dimensions.colors
  ⟨bodyEdges.count, edges.count, rest.count, centers.count,
    dimensions.work + bodyEdges.work + edges.work + rest.work + centers.work + 5⟩

 theorem current_values (security : ℕ) :
    (current security).bodyEdges = Parameters.bodySize security - 1 ∧
    (current security).edges = CurrentAffineGeometry.edgeCount security ∧
    (current security).rest = centerCount security + Parameters.modulus security ∧
    (current security).centers = centerCount security := by
  rcases CurrentProposalDimensions.current_values security with ⟨hq, hl, hb, hd, _, _⟩
  have hroom := ProposalPrimary.population_room security
  have he := LobsterCoordinates.current_edge_count security
  simp only [current, subtractCounter_value, hq, hl, hb, hd]
  constructor
  · trivial
  constructor
  · exact he.symm
  constructor
  · unfold centerCount; omega
  · rfl

attribute [local irreducible] CurrentEmissionMetadata.current

 theorem current_counts (security : ℕ) :
    (current security).bodyEdges + 1 = (CurrentProposalDimensions.current security).body ∧
    (current security).edges + 1 = (CurrentProposalDimensions.current security).dimension ∧
    (CurrentProposalDimensions.current security).legs + (current security).rest = (CurrentProposalDimensions.current security).body ∧
    (CurrentProposalDimensions.current security).legs * 3 + (current security).rest = (current security).edges + 1 ∧
    (current security).centers + (CurrentProposalDimensions.current security).colors = (current security).rest ∧
    (current security).bodyEdges + ((CurrentProposalDimensions.current security).legs + (CurrentProposalDimensions.current security).legs) =
      (current security).edges := by
  rcases CurrentEmissionMetadata.current_values security with ⟨hb, he, hr, hc⟩
  rcases CurrentProposalDimensions.current_values security with ⟨hq, hl, hp, hd, _, _⟩
  have hroom := ProposalPrimary.population_room security
  have hpositive := LobsterCoordinates.current_body_positive security
  have hvertex := LobsterCoordinates.current_vertex_count security
  have hedge := LobsterCoordinates.current_edge_count security
  unfold CurrentAffineGeometry.edgeCount CurrentAffineGeometry.bodyEdges at he
  simp only [hb, he, hr, hc, hq, hl, hp, hd]
  unfold centerCount Parameters.dimension at *
  refine ⟨by omega, hvertex, by omega, ?_, trivial, trivial⟩
  omega


def vertexEquiv (security : ℕ) : Fin ((current security).edges + 1) ≃ Fin (Parameters.dimension security) :=
  finCongr ((current_counts security).2.1.trans (CurrentProposalDimensions.current_values security).2.2.2.1)

def legEquiv (security : ℕ) : Fin (CurrentProposalDimensions.current security).legs ≃ Fin (Parameters.legCount security) :=
  CurrentProposalDimensions.legEquiv security

def restEquiv (security : ℕ) : Fin (current security).rest ≃ Fin (centerCount security + Parameters.modulus security) :=
  finCongr (current_values security).2.2.1


def pointEquiv (security : ℕ) : Sigma (blockSlotsProgram (CurrentProposalDimensions.current security).legs (current security).rest) ≃
    Sigma (Slots security) where
  toFun
    | ⟨.inl leg, slot⟩ => ⟨.inl (legEquiv security leg), slot⟩
    | ⟨.inr body, slot⟩ => match finSumFinEquiv.symm (restEquiv security body) with
      | .inl center => ⟨.inr (.inl center), slot⟩
      | .inr queue => ⟨.inr (.inr queue), slot⟩
  invFun
    | ⟨.inl leg, slot⟩ => ⟨.inl ((legEquiv security).symm leg), slot⟩
    | ⟨.inr (.inl center), slot⟩ => ⟨.inr ((restEquiv security).symm (finSumFinEquiv (.inl center))), slot⟩
    | ⟨.inr (.inr queue), slot⟩ => ⟨.inr ((restEquiv security).symm (finSumFinEquiv (.inr queue))), slot⟩
  left_inv := by
    rintro ⟨leg | body, slot⟩
    · exact Sigma.ext (congrArg Sum.inl ((legEquiv security).symm_apply_apply leg)) (HEq.rfl)
    · obtain ⟨center | queue, h⟩ := finSumFinEquiv.surjective (restEquiv security body)
      all_goals
        simp only [← h, Equiv.symm_apply_apply]
        exact Sigma.ext (congrArg Sum.inr (by rw [h, Equiv.symm_apply_apply])) (HEq.rfl)
  right_inv := by
    rintro ⟨leg | (center | queue), slot⟩
    · exact Sigma.ext (congrArg Sum.inl ((legEquiv security).apply_symm_apply leg)) (HEq.rfl)
    · simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    · simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

 theorem numbering_point (security : ℕ)
    (point : Sigma (blockSlotsProgram (CurrentProposalDimensions.current security).legs (current security).rest)) :
    vertexEquiv security (physicalVertexNumberingProgram _ _ _ (current_counts security).2.2.2.1 point) =
      CurrentPhysicalNumbering.numbering security (pointEquiv security point) := by
  rcases point with ⟨leg | body, slot⟩
  · apply Fin.ext
    change _ = (CurrentPhysicalNumbering.numbering security ⟨.inl (legEquiv security leg), slot⟩).val
    rw [CurrentPhysicalNumbering.numbering_primary]
    change slot.val + 3 * leg.val = slot.val + 3 * leg.val
    rfl
  · change Fin 1 at slot
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    · apply Fin.ext
      change _ = (CurrentPhysicalNumbering.numbering security
        (match finSumFinEquiv.symm (restEquiv security body) with
          | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
          | .inr queue => ⟨.inr (.inr queue), (0 : Fin 1)⟩)).val
      rw [← he, Equiv.symm_apply_apply, CurrentPhysicalNumbering.numbering_center]
      have hv := congrArg Fin.val he
      change center.val = body.val at hv
      change (CurrentProposalDimensions.current security).legs * 3 + (0 + 1 * body.val) = Parameters.legCount security * 3 + center.val
      rw [(CurrentProposalDimensions.current_values security).2.1]
      omega
    · apply Fin.ext
      change _ = (CurrentPhysicalNumbering.numbering security
        (match finSumFinEquiv.symm (restEquiv security body) with
          | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
          | .inr queue => ⟨.inr (.inr queue), (0 : Fin 1)⟩)).val
      rw [← he, Equiv.symm_apply_apply, CurrentPhysicalNumbering.numbering_queue]
      have hv := congrArg Fin.val he
      change centerCount security + queue.val = body.val at hv
      change (CurrentProposalDimensions.current security).legs * 3 + (0 + 1 * body.val) =
        Parameters.legCount security * 3 + (centerCount security + queue.val)
      rw [(CurrentProposalDimensions.current_values security).2.1]
      omega

end CurrentAFT.CurrentEmissionMetadata

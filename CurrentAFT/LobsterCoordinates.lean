import CurrentAFT.LobsterIncidence
import CurrentAFT.Parameters

/-! # Physical vertex and source numbering for the current incidence basis -/
namespace CurrentAFT.LobsterCoordinates
open AFT PublicCharge LobsterIncidence
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def edgeIndex (bodyEdges legs : ℕ) :
    (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) ≃ Fin (bodyEdges + (legs + legs)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def vertexIndex (bodyEdges legs : ℕ) :
    EndpointIndex (bodyEdges + 1) (Fin legs) ≃ Fin (bodyEdges + (legs + legs) + 1) :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))

def edgeCoordinates (Scalar : Type*) [CommRing Scalar] (bodyEdges legs : ℕ) :
    (Fin (bodyEdges + (legs + legs)) → Scalar) ≃ₗ[Scalar]
      ((Fin bodyEdges → Scalar) × ((Fin legs → Scalar) × (Fin legs → Scalar))) :=
  (LinearEquiv.funCongrLeft Scalar Scalar (edgeIndex bodyEdges legs)).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin bodyEdges) (Fin legs ⊕ Fin legs) Scalar Scalar).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
        (LinearEquiv.sumArrowLequivProdArrow (Fin legs) (Fin legs) Scalar Scalar)))

def zeroSumCoordinates {Index : Type*} [Fintype Index] (count : ℕ) (numbering : Index ≃ Fin (count + 1)) :
    zeroSum Index ≃ₗ[ℤ] zeroSumLattice count where
  toFun word := ⟨fun index => word.val (numbering.symm index), by
    change ∑ index, word.val (numbering.symm index) = 0
    rw [Equiv.sum_comp numbering.symm]
    exact word.property⟩
  invFun word := ⟨fun index => word.val (numbering index), by
    change ∑ index, word.val (numbering index) = 0
    rw [Equiv.sum_comp numbering]
    exact word.property⟩
  left_inv word := by apply Subtype.ext; funext index; simp
  right_inv word := by apply Subtype.ext; funext index; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def incidenceBasis (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1)) :
    (Fin (bodyEdges + (legs + legs)) → ℤ) ≃ₗ[ℤ] zeroSumLattice (bodyEdges + (legs + legs)) :=
  (edgeCoordinates ℤ bodyEdges legs).trans
    ((LobsterIncidence.basis placement attachment).trans
      (zeroSumCoordinates _ (vertexIndex bodyEdges legs)))

theorem incidenceBasis_apply (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1)) (input : Fin (bodyEdges + (legs + legs)) → ℤ)
    (vertex : EndpointIndex (bodyEdges + 1) (Fin legs)) :
    (incidenceBasis bodyEdges legs placement attachment input).val (vertexIndex bodyEdges legs vertex) =
      LobsterIncidence.load placement attachment (edgeCoordinates ℤ bodyEdges legs input) vertex := by
  change LobsterIncidence.load placement attachment (edgeCoordinates ℤ bodyEdges legs input)
    ((vertexIndex bodyEdges legs).symm (vertexIndex bodyEdges legs vertex)) = _
  rw [Equiv.symm_apply_apply]

def relabeledBasis (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    (Fin (bodyEdges + (legs + legs)) → ℤ) ≃ₗ[ℤ] zeroSumLattice (bodyEdges + (legs + legs)) :=
  (incidenceBasis bodyEdges legs placement attachment).trans (zeroSumCoordinates _ relabeling)

theorem relabeledBasis_apply (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) (index : Fin (bodyEdges + (legs + legs) + 1)) :
    (relabeledBasis bodyEdges legs placement attachment relabeling input).val index =
      LobsterIncidence.load placement attachment (edgeCoordinates ℤ bodyEdges legs input)
        ((vertexIndex bodyEdges legs).symm (relabeling.symm index)) := rfl

theorem current_body_positive (security : ℕ) : 0 < Parameters.bodySize security := by
  unfold Parameters.bodySize Parameters.scale
  exact Nat.mul_pos (Parameters.modulus_spec security).2.pos (Nat.pow_pos (Nat.pow_pos (Parameters.base_pos security)))

theorem current_edge_count (security : ℕ) :
    (Parameters.bodySize security - 1) + (Parameters.legCount security + Parameters.legCount security) =
      Parameters.dimension security - 1 := by
  have hbody := current_body_positive security
  unfold Parameters.dimension
  omega

theorem current_vertex_count (security : ℕ) :
    (Parameters.bodySize security - 1) + (Parameters.legCount security + Parameters.legCount security) + 1 =
      Parameters.dimension security := by
  have hbody := current_body_positive security
  unfold Parameters.dimension
  omega

end
end CurrentAFT.LobsterCoordinates

import CurrentAFT.AffineRealization
import CurrentAFT.CyclePathClosure

/-! # The actual affine load is the complete endpoint assembly -/
namespace CurrentAFT.LobsterAffineLoad
open AFT PublicCharge LobsterCoordinates LobsterMixerMatrix AffineBaseline AffineRealization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem mixed_coordinates (bodyEdges legs : ℕ) (scale shear : Fin legs → ℤ)
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) :
    edgeCoordinates ℤ bodyEdges legs ((numberedMatrix bodyEdges legs scale shear).mulVec input) =
      ((edgeCoordinates ℤ bodyEdges legs input).1,
        (fun leg => scale leg * (edgeCoordinates ℤ bodyEdges legs input).2.1 leg +
          shear leg * (edgeCoordinates ℤ bodyEdges legs input).2.2 leg,
         (edgeCoordinates ℤ bodyEdges legs input).2.2)) := by
  apply Prod.ext
  · funext vertex
    change (numberedMatrix bodyEdges legs scale shear).mulVec input (edgeIndex bodyEdges legs (.inl vertex)) = _
    rw [numberedMatrix_action, blockMatrix_action]
    rfl
  · apply Prod.ext
    · funext leg
      change (numberedMatrix bodyEdges legs scale shear).mulVec input (edgeIndex bodyEdges legs (.inr (.inl leg))) = _
      rw [numberedMatrix_action, blockMatrix_action]
      rfl
    · funext leg
      change (numberedMatrix bodyEdges legs scale shear).mulVec input (edgeIndex bodyEdges legs (.inr (.inr leg))) = _
      rw [numberedMatrix_action, blockMatrix_action]
      rfl

theorem queueColumn_body (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin (bodyEdges + 1)) :
    queueColumn bodyEdges legs modulus queues relabeling (relabeling (vertexIndex bodyEdges legs (.inl vertex))) =
      if vertex ∈ Finset.univ.map queues then 1 else 0 := by
  have hequal : relabeling (vertexIndex bodyEdges legs (.inl vertex)) ∈
      Finset.univ.map (queueEmbedding bodyEdges legs modulus queues relabeling) ↔
      vertex ∈ Finset.univ.map queues := by
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨point, heq⟩
      exact ⟨point, Sum.inl.inj ((vertexIndex bodyEdges legs).injective (relabeling.injective heq))⟩
    · rintro ⟨point, heq⟩
      exact ⟨point, congrArg (fun vertex => relabeling (vertexIndex bodyEdges legs (.inl vertex))) heq⟩
  simp only [queueColumn, hequal]

theorem queueColumn_leg (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin legs ⊕ Fin legs) :
    queueColumn bodyEdges legs modulus queues relabeling (relabeling (vertexIndex bodyEdges legs (.inr vertex))) = 0 := by
  have hnot : relabeling (vertexIndex bodyEdges legs (.inr vertex)) ∉
      Finset.univ.map (queueEmbedding bodyEdges legs modulus queues relabeling) := by
    intro hmem
    obtain ⟨point, _, heq⟩ := Finset.mem_map.mp hmem
    have h := (vertexIndex bodyEdges legs).injective (relabeling.injective heq)
    cases h
  exact if_neg hnot

def primary (bodyEdges legs : ℕ) (scale shear intercept : Fin legs → ℤ)
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) : Fin legs → ℤ :=
  fun leg => intercept leg + scale leg * (edgeCoordinates ℤ bodyEdges legs input).2.1 leg +
    shear leg * (edgeCoordinates ℤ bodyEdges legs input).2.2 leg

/-- Every integer input, the same second leg input, and the one shared
queue are retained in this pointwise identity. -/
theorem actual_endpoint_load (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear intercept : Fin legs → ℤ) (centers : Fin (bodyEdges + 1) → ℤ) (shift : Fin legs → ℤ)
    (closureScalar : ℤ) (hcharge : PublicChargeTest modulus centers shift)
    (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ)
    (vertex : EndpointIndex (bodyEdges + 1) (Fin legs)) :
    roundingLoad _ (injectionColumn _ modulus)
      (linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input +
        offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge)
      (relabeling (vertexIndex bodyEdges legs vertex)) =
      assembledEndpoint centers shift ((modulus : ℤ) - 1)
        (Fin.snoc (edgeCoordinates ℤ bodyEdges legs input.1).1 closureScalar) placement attachment
        (edgeCoordinates ℤ bodyEdges legs input.1).2.2
        (primary bodyEdges legs scale shear intercept input.1) (Finset.univ.map queues) input.2 vertex := by
  rw [affine_load]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, relabeledBasis_apply,
    Equiv.symm_apply_apply, numberedOffset, offset]
  rw [mixed_coordinates]
  rcases vertex with vertex | (leg | leg)
  · rw [queueColumn_body]
    simp only [LobsterIncidence.load, baseline, Sum.elim_inl, Pi.add_apply, assembledEndpoint,
      CyclePathClosure.cycle_eq_path_closure, Pi.add_apply, queueIncrement]
    split_ifs <;> ring
  · rw [queueColumn_leg]
    simp [LobsterIncidence.load, baseline, assembledEndpoint, primary]
    ring
  · rw [queueColumn_leg]
    simp [LobsterIncidence.load, baseline, assembledEndpoint, primary, legCompanion]
    ring

end
end CurrentAFT.LobsterAffineLoad

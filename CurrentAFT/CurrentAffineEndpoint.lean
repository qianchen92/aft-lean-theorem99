import CurrentAFT.CurrentSourceLayout
import CurrentAFT.CurrentAffineLoad
import CurrentAFT.LobsterAffineLoad

/-! # The actual dimension-indexed affine map has the natural endpoint load

This pointwise integer identity uses the same two inputs at each leg,
the same closing edge at the body wraparound, and the single shared queue.
The final index is precisely the physical-slot flattening followed by
the core's endpoint permutation.
-/
namespace CurrentAFT.CurrentAffineEndpoint

open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentSourceProtection CurrentSourceLayout
  PublicEndpointPlacement PublicCharge LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

private theorem assembled_finCongr {body other : ℕ} (heq : body = other)
    (centers latent : Fin body → ℤ) {Leg : Type*} [Fintype Leg]
    (shift second primary : Leg → ℤ) (legConstant : ℤ) (permutation : Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) {count : ℕ} (queue : Fin count ↪ Fin body) (scalar : ℤ)
    (vertex : EndpointIndex body Leg) :
    assembledEndpoint (fun index => centers ((finCongr heq).symm index)) shift legConstant
      (fun index => latent ((finCongr heq).symm index))
      ((finCongr heq).symm.trans (permutation.trans (finCongr heq)))
      (fun leg => finCongr heq (attachment leg)) second primary
      (Finset.univ.map (queue.trans (finCongr heq).toEmbedding)) scalar
      (Sum.map (finCongr heq) id vertex) =
        assembledEndpoint centers shift legConstant latent permutation attachment second primary
          (Finset.univ.map queue) scalar vertex := by
  subst other
  simp
  rfl

def primaryOutput (security : ℕ) (scale shear intercept : Fin (Parameters.legCount security) → ℤ)
    (word : Fin (sourceCount security) → ℤ) : Fin (Parameters.legCount security) → ℤ :=
  fun leg => intercept leg + scale leg * firstInput security word leg +
    shear leg * secondInput security word leg

/-- The current natural assembly, before its already specified physical
flattening and final endpoint relabeling. -/
def naturalAssembly (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (scale shear intercept : Fin (Parameters.legCount security) → ℤ)
    (word : Fin (sourceCount security) → ℤ) : AssemblyIndex security → ℤ :=
  assembledEndpoint (centerAt security layout core) (legShift security core)
    ((Parameters.modulus security : ℤ) - 1) (bodyLatent security word) core.bodyPermutation
    (attachmentPosition security layout) (secondInput security word)
    (primaryOutput security scale shear intercept word) (queueSet security layout) (queueInput security word)

theorem affine_endpoint (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (scale shear intercept : Fin (Parameters.legCount security) → ℤ)
    (hcharge : publicCharge security core) (word : Fin (sourceCount security) → ℤ)
    (vertex : AssemblyIndex security) :
    rounding security
      ((CurrentAffineGeometry.matrix security layout core scale shear).mulVec (hiddenWord security word) +
        CurrentAffineGeometry.offset security layout core intercept (closureScalar security word) hcharge)
      (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
        naturalAssembly security layout core scale shear intercept word vertex := by
  letI : NeZero (Parameters.modulus security) := ⟨(Parameters.modulus_spec security).2.ne_zero⟩
  have hindex : (dimensionEquiv security).symm
      (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
        relabeling security layout core (vertexIndex (bodyEdges security) (Parameters.legCount security)
          (Sum.map (bodyEquiv security) id vertex)) := by
    apply (dimensionEquiv security).injective
    rw [Equiv.apply_symm_apply]
    change core.endpointPermutation.symm (endpointFlatten security layout vertex) =
      dimensionEquiv security (relabeling security layout core (naturalNumbering security vertex))
    exact (relabeling_natural security layout core vertex).symm
  unfold rounding
  rw [split_add, matrix_split, offset_split, hindex]
  rw [LobsterAffineLoad.actual_endpoint_load]
  change assembledEndpoint (centers security layout core) (legShift security core)
    ((Parameters.modulus security : ℤ) - 1)
    (Fin.snoc (edgeCoordinates ℤ (bodyEdges security) (Parameters.legCount security)
      (hiddenCoordinates security word).1).1 (closureScalar security word))
    (placement security core) (attachments security layout)
    (edgeCoordinates ℤ (bodyEdges security) (Parameters.legCount security)
      (hiddenCoordinates security word).1).2.2
    (LobsterAffineLoad.primary (bodyEdges security) (Parameters.legCount security)
      scale shear intercept (hiddenCoordinates security word).1)
    (Finset.univ.map (queues security layout)) (hiddenCoordinates security word).2
    (Sum.map (bodyEquiv security) id vertex) = _
  rw [bodyLatent_from_hidden, hiddenCoordinates_second, hiddenCoordinates_queue]
  have hprimary : LobsterAffineLoad.primary (bodyEdges security) (Parameters.legCount security)
      scale shear intercept (hiddenCoordinates security word).1 =
        primaryOutput security scale shear intercept word := by
    unfold LobsterAffineLoad.primary primaryOutput
    rw [hiddenCoordinates_first, hiddenCoordinates_second]
  rw [hprimary]
  exact assembled_finCongr (by have := current_body_positive security; dsimp only [bodyEdges]; omega)
    (centerAt security layout core) (bodyLatent security word) (legShift security core)
    (secondInput security word) (primaryOutput security scale shear intercept word)
    ((Parameters.modulus security : ℤ) - 1) core.bodyPermutation
    (attachmentPosition security layout) (queuePosition security layout) (queueInput security word) vertex

theorem load_natural (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (scale shear intercept : Fin (Parameters.legCount security) → ℤ)
    (hcharge : publicCharge security core) (word : Fin (sourceCount security) → ℤ)
    (vertex : AssemblyIndex security) :
    CurrentAffineLoad.load security layout core scale shear intercept (closureScalar security word)
      (hiddenWord security word) (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
        naturalAssembly security layout core scale shear intercept word vertex := by
  rw [← affine_rounding security layout core scale shear intercept (closureScalar security word) hcharge]
  exact affine_endpoint security layout core scale shear intercept hcharge word vertex

end
end CurrentAFT.CurrentAffineEndpoint

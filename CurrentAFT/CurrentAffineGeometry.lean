import CurrentAFT.AffineRealization
import CurrentAFT.CyclePathClosure
import CurrentAFT.PublicEndpointPlacement
import CurrentAFT.ActualPublicCharge

/-! # Current public-core geometry and actual integral affine data -/
namespace CurrentAFT.CurrentAffineGeometry
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  LobsterCoordinates AffineRealization PublicEndpointPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev bodyEdges (security : ℕ) := Parameters.bodySize security - 1
abbrev edgeCount (security : ℕ) := bodyEdges security + (Parameters.legCount security + Parameters.legCount security)

def bodyEquiv (security : ℕ) : BodyIndex security ≃ Fin (bodyEdges security + 1) :=
  finCongr (by have := current_body_positive security; dsimp only [bodyEdges]; omega)

def dimensionEquiv (security : ℕ) : Fin (edgeCount security + 1) ≃ Fin (Parameters.dimension security) :=
  finCongr (current_vertex_count security)

def naturalNumbering (security : ℕ) : AssemblyIndex security ≃ Fin (edgeCount security + 1) :=
  (Equiv.sumCongr (bodyEquiv security) (Equiv.refl _)).trans
    (vertexIndex (bodyEdges security) (Parameters.legCount security))

/-- The final relabeling includes the actual physical-slot flattening. -/
def relabeling (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    Equiv.Perm (Fin (edgeCount security + 1)) :=
  (naturalNumbering security).symm.trans ((endpointFlatten security layout).trans
    (core.endpointPermutation.symm.trans (dimensionEquiv security).symm))

theorem relabeling_natural (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (vertex : AssemblyIndex security) :
    dimensionEquiv security (relabeling security layout core (naturalNumbering security vertex)) =
      core.endpointPermutation.symm (endpointFlatten security layout vertex) := by
  simp [relabeling]

def placement (security : ℕ) (core : Core security) : Equiv.Perm (Fin (bodyEdges security + 1)) :=
  (bodyEquiv security).symm.trans (core.bodyPermutation.trans (bodyEquiv security))

def queues (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Fin (Parameters.modulus security) ↪ Fin (bodyEdges security + 1) :=
  (queuePosition security layout).trans (bodyEquiv security).toEmbedding

def attachments (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Fin (Parameters.legCount security) → Fin (bodyEdges security + 1) :=
  fun leg => bodyEquiv security (attachmentPosition security layout leg)

def centers (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    Fin (bodyEdges security + 1) → ℤ :=
  fun vertex => centerAt security layout core ((bodyEquiv security).symm vertex)

theorem centers_charge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (hcharge : publicCharge security core) :
    PublicCharge.PublicChargeTest (Parameters.modulus security) (centers security layout core)
      (legShift security core) := by
  have h := (publicCharge_iff security layout core).mpr hcharge
  unfold PublicCharge.PublicChargeTest centers at *
  rw [Equiv.sum_comp (bodyEquiv security).symm]
  exact h

def unitToFinOne : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv input := by cases input; rfl
  right_inv input := (Fin.eq_zero input).symm

/-- Edge coordinates precede the one queue coordinate, as in the fixed
rounding matrix `[pathIncidence | injectionColumn]`. -/
def coordinateNumbering (security : ℕ) : (Fin (edgeCount security) ⊕ Unit) ≃ Fin (Parameters.dimension security) :=
  ((Equiv.sumCongr (Equiv.refl _) unitToFinOne).trans finSumFinEquiv).trans (dimensionEquiv security)

def matrix (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) :
    Matrix (Fin (Parameters.dimension security)) (Fin (Parameters.dimension security)) ℤ :=
  Matrix.reindex (coordinateNumbering security) (coordinateNumbering security)
    (AffineRealization.matrix (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security)
      (queues security layout) (placement security core) (attachments security layout)
      (relabeling security layout core) scale shear)

theorem matrix_invertible (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ)
    (hscale : ∀ leg, (scale leg : ZMod (Parameters.modulus security)) ≠ 0) :
    IsUnit ((matrix security layout core scale shear).map (Int.castRingHom (ZMod (Parameters.modulus security)))) := by
  letI : Fact (Parameters.modulus security).Prime := ⟨(Parameters.modulus_spec security).2⟩
  have h := AffineRealization.matrix_modular_invertible (bodyEdges security) (Parameters.legCount security)
    (Parameters.modulus security) (queues security layout) (placement security core) (attachments security layout)
    (relabeling security layout core) scale shear hscale
  exact h.map (Matrix.reindexAlgEquiv (ZMod (Parameters.modulus security))
    (ZMod (Parameters.modulus security)) (coordinateNumbering security)).toMonoidHom

def offset (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (hcharge : publicCharge security core) : Fin (Parameters.dimension security) → ℤ := by
  letI : NeZero (Parameters.modulus security) := ⟨(Parameters.modulus_spec security).2.ne_zero⟩
  let value := AffineRealization.offsetCoordinates (bodyEdges security) (Parameters.legCount security)
    (Parameters.modulus security) (queues security layout) (centers security layout core)
    (legShift security core) intercept (placement security core) closureScalar (relabeling security layout core)
    (centers_charge security layout core hcharge)
  exact fun index => Sum.elim value.1 (fun _ : Unit => value.2) ((coordinateNumbering security).symm index)

end
end CurrentAFT.CurrentAffineGeometry

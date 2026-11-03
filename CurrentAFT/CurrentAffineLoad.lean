import CurrentAFT.CurrentAffineGeometry

/-! # The actual dimension-indexed matrix has the exact integral vertex load -/
namespace CurrentAFT.CurrentAffineLoad
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def splitSource (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :
    (Fin (edgeCount security) → ℤ) × ℤ :=
  (fun edge => input (coordinateNumbering security (.inl edge)),
    input (coordinateNumbering security (.inr ())))

def packSource (security : ℕ) (input : (Fin (edgeCount security) → ℤ) × ℤ) :
    Fin (Parameters.dimension security) → ℤ :=
  fun index => Sum.elim input.1 (fun _ : Unit => input.2) ((coordinateNumbering security).symm index)

theorem split_pack (security : ℕ) (input : (Fin (edgeCount security) → ℤ) × ℤ) :
    splitSource security (packSource security input) = input := by
  simp [splitSource, packSource]

theorem pack_split (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :
    packSource security (splitSource security input) = input := by
  funext index
  obtain ⟨edge | point, rfl⟩ := (coordinateNumbering security).surjective index
  · simp [packSource, splitSource]
  · cases point
    simp [packSource, splitSource]

theorem split_add (security : ℕ) (first second : Fin (Parameters.dimension security) → ℤ) :
    splitSource security (first + second) = splitSource security first + splitSource security second := rfl

theorem matrix_action (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ) :
    (CurrentAffineGeometry.matrix security layout core scale shear).mulVec input =
      packSource security
        (AffineRealization.linearPart (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security)
          (queues security layout) (placement security core) (attachments security layout)
          (relabeling security layout core) scale shear (splitSource security input)) := by
  change (Matrix.reindex _ _ _).mulVecLin input = _
  rw [Matrix.mulVecLin_reindex]
  change (fun index => (AffineRealization.matrix (bodyEdges security) (Parameters.legCount security)
    (Parameters.modulus security) (queues security layout) (placement security core) (attachments security layout)
      (relabeling security layout core) scale shear).mulVec (input ∘ coordinateNumbering security)
        ((coordinateNumbering security).symm index)) = _
  have hinput : input ∘ coordinateNumbering security =
      Sum.elim (splitSource security input).1 (fun _ : Unit => (splitSource security input).2) := by
    funext index
    rcases index with edge | point
    · rfl
    · cases point; rfl
  rw [hinput, AffineRealization.matrix_action]
  rfl

theorem matrix_split (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ) :
    splitSource security ((CurrentAffineGeometry.matrix security layout core scale shear).mulVec input) =
      AffineRealization.linearPart (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security)
        (queues security layout) (placement security core) (attachments security layout)
        (relabeling security layout core) scale shear (splitSource security input) := by
  rw [matrix_action, split_pack]

theorem offset_split (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (hcharge : publicCharge security core) :
    splitSource security (CurrentAffineGeometry.offset security layout core intercept closureScalar hcharge) =
      AffineRealization.offsetCoordinates (bodyEdges security) (Parameters.legCount security)
        (Parameters.modulus security) (queues security layout) (centers security layout core)
        (legShift security core) intercept (placement security core) closureScalar (relabeling security layout core)
        (centers_charge security layout core hcharge) := by
  exact split_pack security _

/-- The fixed rounding map, with the path columns first and the charge
injection column last. It is independent of all sampled public data. -/
def rounding (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :
    Fin (Parameters.dimension security) → ℤ :=
  fun vertex => roundingLoad (edgeCount security) (injectionColumn _ (Parameters.modulus security))
    (splitSource security input) ((dimensionEquiv security).symm vertex)

def load (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear intercept : Fin (Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (input : Fin (Parameters.dimension security) → ℤ) : Fin (Parameters.dimension security) → ℤ :=
  fun vertex =>
    ((relabeledBasis (bodyEdges security) (Parameters.legCount security)
        (placement security core) (attachments security layout) (relabeling security layout core)
        ((numberedMatrix (bodyEdges security) (Parameters.legCount security) scale shear).mulVec
          (splitSource security input).1)).val +
      (splitSource security input).2 • AffineRealization.queueColumn (bodyEdges security) (Parameters.legCount security)
        (Parameters.modulus security) (queues security layout) (relabeling security layout core) +
      numberedOffset (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security)
        (centers security layout core) (legShift security core) intercept (placement security core) closureScalar
        (relabeling security layout core)) ((dimensionEquiv security).symm vertex)

theorem affine_rounding (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear intercept : Fin (Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (hcharge : publicCharge security core) (input : Fin (Parameters.dimension security) → ℤ) :
    rounding security ((CurrentAffineGeometry.matrix security layout core scale shear).mulVec input +
      CurrentAffineGeometry.offset security layout core intercept closureScalar hcharge) =
        load security layout core scale shear intercept closureScalar input := by
  unfold rounding
  rw [split_add, matrix_split, offset_split, AffineRealization.affine_load]
  rfl

end
end CurrentAFT.CurrentAffineLoad

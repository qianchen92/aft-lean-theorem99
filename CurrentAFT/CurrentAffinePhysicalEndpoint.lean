import CurrentAFT.CurrentAffineProtectedCarry
import CurrentAFT.ActualAffineCompletedOutput

/-! # Actual protected affine endpoints are the completed physical output

The physical word below is evaluated from the real completed public charts
and the same protected first/second sources. Its block coordinates are the
ones of `ActualAffineCompletedOutput`, before the existing flattening and
endpoint permutation.
-/
namespace CurrentAFT.CurrentAffinePhysicalEndpoint

open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge ActualBlockFock
  ActualBlockMean CurrentSourceProtection CurrentSourceLayout CurrentAffineEndpoint
  CurrentAffineGeometry CurrentAffineData CurrentAffineLegCarry CurrentAffineProtectedCarry
  GaussianProductProtection PublicEndpointPlacement AffineFlagCalibration ProposalPrimary
  PublicCoefficientOutput
open HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def blockWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : Charts security) (word : ProtectedWord (cutoff security)) :
    Sigma (Slots security) → RefinedPublicOutput.Palette security
  | ⟨.inl leg, slot⟩ => evaluateTriple security
      (attachmentRoots security layout core.bodyPermutation (protectedBody security word) leg)
      (core.controls (.inl leg)).1 (core.legs leg) (charts leg)
      (protectedFirst security word leg) (protectedSecond security word leg) slot
  | ⟨.inr (.inl center), _⟩ => shiftEquiv security
      (centerRoots security layout core.bodyPermutation (protectedBody security word) center)
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val
  | ⟨.inr (.inr point), _⟩ => shiftEquiv security
      (queueRoots security layout core.bodyPermutation (protectedBody security word) point +
        queueInput security (sourceEmbedding (cutoff security) word)) (core.queueBaselines point)

def outputWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : Charts security) (word : ProtectedWord (cutoff security)) :
    Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security :=
  AFT.relabel (renameWord (flatten security) (blockWord security layout core charts word)) core.endpointPermutation

theorem integerPrimary_embed (security : ℕ) (chart : PublicChart security)
    (first second : Scalar security) :
    (integerPrimary security chart first.val second.val : RefinedPublicOutput.Residue security) =
      RefinedPublicOutput.embed security (evaluatePrimary security chart first second) := by
  exact (integerPrimary_cast security chart first.val second.val).trans
    (RingEquiv.apply_symm_apply (ZMod.finEquiv (Parameters.modulus security)) _).symm

theorem integerCompanion_embed (security : ℕ) (shift : ℤ) (chart : PublicChart security)
    (first second : Scalar security) :
    (integerCompanion security shift chart first.val second.val : RefinedPublicOutput.Residue security) =
      RefinedPublicOutput.embed security
        (companion security (shift - second.val) (evaluatePrimary security chart first second)) := by
  have hcomp : RefinedPublicOutput.embed security
      (companion security (shift - second.val) (evaluatePrimary security chart first second)) =
        -1 + ((shift - second.val : ℤ) : RefinedPublicOutput.Residue security) -
          RefinedPublicOutput.embed security (evaluatePrimary security chart first second) :=
    RingEquiv.apply_symm_apply (ZMod.finEquiv (Parameters.modulus security)) _
  rw [hcomp]
  rw [← integerPrimary_embed]
  unfold integerCompanion
  push_cast
  rw [ZMod.natCast_self]
  ring

theorem evaluateTriple_attachment (security : ℕ) (root : ℤ) (primary : RefinedPublicOutput.Palette security)
    (seed : LegCore security) (chart : PublicChart security) (first second : Scalar security) :
    evaluateTriple security root primary seed chart first second 2 =
      shiftEquiv security (root + second.val) seed.2 := by
  exact congrArg Prod.snd (PhysicalBlockTensors.tripleEquiv.apply_symm_apply
    (pairProjection security (ActualPublicLegCharge.publicShift security primary seed.1 - second.val)
      (evaluatePrimary security chart first second), shiftEquiv security (root + second.val) seed.2))

private theorem body_formula (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : Charts security) (word : ProtectedWord (cutoff security))
    (vertex : BodyIndex security) :
    naturalAssembly security layout core (scales security charts) (shears security charts)
      (intercepts security charts) (sourceEmbedding (cutoff security) word) (.inl vertex) =
    centerAt security layout core vertex +
      rootAt security core.bodyPermutation (protectedBody security word) vertex +
        bodyExtra security layout (sourceEmbedding (cutoff security) word) vertex := by
  have hroot : rootAt security core.bodyPermutation (protectedBody security word) vertex =
      PublicCharge.cycleDifference (bodyLatent security (sourceEmbedding (cutoff security) word))
        (core.bodyPermutation.symm vertex) := rfl
  rw [hroot]
  unfold naturalAssembly PublicCharge.assembledEndpoint bodyExtra
  ring

theorem natural_mod_block (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : Charts security) (word : ProtectedWord (cutoff security))
    (vertex : AssemblyIndex security) :
    (naturalAssembly security layout core (scales security charts) (shears security charts)
      (intercepts security charts) (sourceEmbedding (cutoff security) word) vertex :
      RefinedPublicOutput.Residue security) =
    RefinedPublicOutput.embed security
      (blockWord security layout core charts word (toPhysical security layout vertex)) := by
  rcases vertex with vertex | (leg | leg)
  · rw [body_formula]
    obtain ⟨center | (point | leg), rfl⟩ := layout.surjective vertex
    · rw [bodyExtra_center]
      simp only [centerAt, toPhysical, Equiv.symm_apply_apply, blockWord,
        centerRoots]
      rw [RefinedPublicOutput.embed_shift, RefinedPublicOutput.embed_value]
      push_cast
      ring
    · rw [bodyExtra_queue]
      simp only [centerAt, toPhysical, Equiv.symm_apply_apply, blockWord,
        queueRoots]
      rw [RefinedPublicOutput.embed_shift, RefinedPublicOutput.embed_value]
      push_cast
      ring
    · rw [bodyExtra_attachment]
      simp only [centerAt, toPhysical, Equiv.symm_apply_apply, blockWord]
      rw [evaluateTriple_attachment]
      rw [RefinedPublicOutput.embed_shift, RefinedPublicOutput.embed_value]
      push_cast
      exact add_assoc _ _ _
  · change (primaryOutput security (scales security charts) (shears security charts)
      (intercepts security charts) (sourceEmbedding (cutoff security) word) leg :
      RefinedPublicOutput.Residue security) =
        RefinedPublicOutput.embed security
          (evaluatePrimary security (charts leg) (protectedFirst security word leg) (protectedSecond security word leg))
    exact integerPrimary_embed security (charts leg) (protectedFirst security word leg) (protectedSecond security word leg)
  · change (integerCompanion security (legShift security core leg) (charts leg)
      (protectedFirst security word leg).val (protectedSecond security word leg).val :
      RefinedPublicOutput.Residue security) =
        RefinedPublicOutput.embed security
          (companion security (legShift security core leg - (protectedSecond security word leg).val)
            (evaluatePrimary security (charts leg) (protectedFirst security word leg) (protectedSecond security word leg)))
    exact integerCompanion_embed security (legShift security core leg) (charts leg)
      (protectedFirst security word leg) (protectedSecond security word leg)

theorem outputWord_at_natural (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : Charts security) (word : ProtectedWord (cutoff security))
    (vertex : AssemblyIndex security) :
    outputWord security layout core charts word (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
      blockWord security layout core charts word (toPhysical security layout vertex) := by
  simp [outputWord, AFT.relabel, renameWord, endpointFlatten, endpointEquiv]

/-- The real affine rounding output, reduced modulo `q`, is exactly the
real completed-chart endpoint word at every protected input. -/
theorem affine_mod_output (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : Charts security) (hcharge : publicCharge security core)
    (word : ProtectedWord (cutoff security)) :
    (fun index => (CurrentAffineLoad.rounding security
      ((CurrentAffineGeometry.matrix security layout core (scales security charts) (shears security charts)).mulVec
        (hiddenWord security (sourceEmbedding (cutoff security) word)) +
      CurrentAffineGeometry.offset security layout core (intercepts security charts)
        (closureScalar security (sourceEmbedding (cutoff security) word)) hcharge) index :
      RefinedPublicOutput.Residue security)) =
    fun index => RefinedPublicOutput.embed security (outputWord security layout core charts word index) := by
  funext index
  obtain ⟨vertex, rfl⟩ := ((endpointFlatten security layout).trans core.endpointPermutation.symm).surjective index
  change (CurrentAffineLoad.rounding security _
    (core.endpointPermutation.symm (endpointFlatten security layout vertex)) : RefinedPublicOutput.Residue security) = _
  simp only [Equiv.trans_apply]
  rw [affine_endpoint, outputWord_at_natural]
  exact natural_mod_block security layout core charts word vertex

end
end CurrentAFT.CurrentAffinePhysicalEndpoint

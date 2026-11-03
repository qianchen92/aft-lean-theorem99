import CurrentAFT.CurrentAffineEndpoint
import CurrentAFT.CurrentAffineData
import CurrentAFT.CurrentPublicSupport

/-! # Total carry cancellation for the actual protected affine inputs

Every body coordinate has zero integer carry. Each leg's two off-body
coordinates have cancelling carries for every supported public chart.
The final physical flattening and endpoint permutation preserve their sum.
-/
namespace CurrentAFT.CurrentAffineProtectedCarry

open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge PublicCharge
  CurrentSourceProtection CurrentSourceLayout CurrentAffineEndpoint CurrentAffineGeometry
  CurrentAffineData CurrentAffineLegCarry CurrentPublicSupport GaussianProductProtection
  PublicEndpointPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def protectedFirst (security : ℕ) (word : ProtectedWord (cutoff security))
    (leg : Fin (Parameters.legCount security)) : AffineFlagCalibration.Scalar security :=
  protectedAux security word (auxNumbering security (.inl (.inl leg)))

def protectedSecond (security : ℕ) (word : ProtectedWord (cutoff security))
    (leg : Fin (Parameters.legCount security)) : AffineFlagCalibration.Scalar security :=
  protectedAux security word (auxNumbering security (.inl (.inr leg)))

theorem primaryOutput_chart (security : ℕ) (charts : Charts security)
    (word : Fin (sourceCount security) → ℤ) (leg : Fin (Parameters.legCount security)) :
    primaryOutput security (scales security charts) (shears security charts) (intercepts security charts) word leg =
      integerPrimary security (charts leg) (firstInput security word leg) (secondInput security word leg) := rfl

def bodyExtra (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (word : Fin (sourceCount security) → ℤ) (vertex : BodyIndex security) : ℤ :=
  attachmentIncrement (attachmentPosition security layout) (secondInput security word) vertex +
    queueIncrement (queueSet security layout) (queueInput security word) vertex

theorem bodyExtra_center (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (word : Fin (sourceCount security) → ℤ) (center : Fin (ActualBlockFock.centerCount security)) :
    bodyExtra security layout word (layout (.inl center)) = 0 := by
  simp [bodyExtra, attachmentIncrement, attachmentPosition, queueIncrement, queueSet, queuePosition]

theorem bodyExtra_queue (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (word : Fin (sourceCount security) → ℤ) (point : Fin (Parameters.modulus security)) :
    bodyExtra security layout word (layout (.inr (.inl point))) = queueInput security word := by
  simp [bodyExtra, attachmentIncrement, attachmentPosition, queueIncrement, queueSet, queuePosition]

theorem bodyExtra_attachment (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (word : Fin (sourceCount security) → ℤ) (leg : Fin (Parameters.legCount security)) :
    bodyExtra security layout word (layout (.inr (.inr leg))) = secondInput security word leg := by
  simp [bodyExtra, attachmentIncrement, attachmentPosition, queueIncrement, queueSet, queuePosition]

theorem protected_root_bound (security : ℕ) (word : ProtectedWord (cutoff security))
    (permutation : Equiv.Perm (BodyIndex security)) (vertex : BodyIndex security) :
    |cycleDifference (bodyLatent security (sourceEmbedding (cutoff security) word))
      (permutation.symm vertex)| < Parameters.sourceCutoff security := by
  simpa only [Equiv.refl_symm, Equiv.refl_apply] using
    protectedCycle_bound security word (Equiv.refl _) (permutation.symm vertex)

theorem protected_root_aux_bound (security : ℕ) (word : ProtectedWord (cutoff security))
    (permutation : Equiv.Perm (BodyIndex security)) (vertex : BodyIndex security)
    (index : Fin (Parameters.legCount security * 2 + 1)) :
    |cycleDifference (bodyLatent security (sourceEmbedding (cutoff security) word))
      (permutation.symm vertex) + (protectedAux security word index).val| <
        Parameters.safeMargin security := by
  simpa only [Equiv.refl_symm, Equiv.refl_apply] using
    protected_load_bound security word (Equiv.refl _) (permutation.symm vertex) index

theorem body_increment_bound (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (word : ProtectedWord (cutoff security)) (vertex : BodyIndex security) :
    |cycleDifference (bodyLatent security (sourceEmbedding (cutoff security) word))
      (core.bodyPermutation.symm vertex) +
      bodyExtra security layout (sourceEmbedding (cutoff security) word) vertex| ≤
        Parameters.safeMargin security := by
  obtain ⟨center | (point | leg), rfl⟩ := layout.surjective vertex
  · rw [bodyExtra_center, add_zero]
    have hroot := protected_root_bound security word core.bodyPermutation (layout (.inl center))
    have hp := sourceCutoff_pos security
    unfold Parameters.safeMargin
    push_cast
    omega
  · rw [bodyExtra_queue]
    exact (protected_root_aux_bound security word core.bodyPermutation
      (layout (.inr (.inl point))) (Fin.last (Parameters.legCount security * 2))).le
  · rw [bodyExtra_attachment]
    exact (protected_root_aux_bound security word core.bodyPermutation
      (layout (.inr (.inr leg))) (auxNumbering security (.inl (.inr leg)))).le

theorem natural_body_carry_zero (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (hsafe : SafeCore security core) (charts : Charts security)
    (word : ProtectedWord (cutoff security)) (vertex : BodyIndex security) :
    naturalAssembly security layout core (scales security charts) (shears security charts)
      (intercepts security charts) (sourceEmbedding (cutoff security) word) (.inl vertex) /
        Parameters.modulus security = 0 := by
  have h := (body_carry_zero security layout core hsafe vertex _
    (body_increment_bound security layout core word vertex)).1
  convert h using 1
  unfold naturalAssembly assembledEndpoint bodyExtra
  congr 1
  ring

theorem natural_paired_carry_zero (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : Charts security)
    (hcharts : ∀ leg, (AffineFlagCalibration.completionLaw security (core.controls (.inl leg)).1
      (core.legs leg).1).weight (charts leg) ≠ 0)
    (word : ProtectedWord (cutoff security)) (leg : Fin (Parameters.legCount security)) :
    naturalAssembly security layout core (scales security charts) (shears security charts)
      (intercepts security charts) (sourceEmbedding (cutoff security) word) (.inr (.inl leg)) /
        Parameters.modulus security +
    naturalAssembly security layout core (scales security charts) (shears security charts)
      (intercepts security charts) (sourceEmbedding (cutoff security) word) (.inr (.inr leg)) /
        Parameters.modulus security = 0 := by
  exact paired_carry_zero security (core.controls (.inl leg)).1 (core.legs leg).1
    (charts leg) (hcharts leg) (protectedFirst security word leg) (protectedSecond security word leg)

theorem natural_total_carry_zero (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (hsafe : SafeCore security core) (charts : Charts security)
    (hcharts : ∀ leg, (AffineFlagCalibration.completionLaw security (core.controls (.inl leg)).1
      (core.legs leg).1).weight (charts leg) ≠ 0)
    (word : ProtectedWord (cutoff security)) :
    (∑ vertex : AssemblyIndex security,
      naturalAssembly security layout core (scales security charts) (shears security charts)
        (intercepts security charts) (sourceEmbedding (cutoff security) word) vertex /
          Parameters.modulus security) = 0 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  simp only [natural_body_carry_zero security layout core hsafe charts word, Finset.sum_const_zero, zero_add]
  exact Finset.sum_eq_zero (fun leg _ => natural_paired_carry_zero security layout core charts hcharts word leg)

theorem affine_total_carry_zero (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (hcharge : publicCharge security core) (hsafe : SafeCore security core)
    (charts : Charts security)
    (hcharts : ∀ leg, (AffineFlagCalibration.completionLaw security (core.controls (.inl leg)).1
      (core.legs leg).1).weight (charts leg) ≠ 0)
    (word : ProtectedWord (cutoff security)) :
    (∑ vertex : Fin (Parameters.dimension security), CurrentAffineLoad.rounding security
      ((CurrentAffineGeometry.matrix security layout core (scales security charts) (shears security charts)).mulVec
        (hiddenWord security (sourceEmbedding (cutoff security) word)) +
      CurrentAffineGeometry.offset security layout core (intercepts security charts)
        (closureScalar security (sourceEmbedding (cutoff security) word)) hcharge) vertex /
        Parameters.modulus security) = 0 := by
  rw [← Equiv.sum_comp ((endpointFlatten security layout).trans core.endpointPermutation.symm)]
  simp only [Equiv.trans_apply, affine_endpoint]
  exact natural_total_carry_zero security layout core hsafe charts hcharts word

end
end CurrentAFT.CurrentAffineProtectedCarry

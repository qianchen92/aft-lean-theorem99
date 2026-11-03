import CurrentAFT.CurrentLinearPhysicalLoad

/-! The actual affine offset has exactly the executed physical baseline
and closure load before the final endpoint permutation. -/
namespace CurrentAFT.CurrentOffsetPhysicalLoad
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentAffineEmissionBridge PublicEndpointPlacement
  LobsterCoordinates AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def rootLoad (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scalar : ℤ) (role : RoleIndex security) : ℤ :=
  centerAt security layout core (layout role) + closure (bodyEdges security) scalar
    (CurrentAffineGeometry.bodyEquiv security (core.bodyPermutation.symm (layout role)))

def physical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (scalar : ℤ) : Sigma (Slots security) → ℤ
  | ⟨.inl leg, slot⟩ => ![intercept leg, (Parameters.modulus security : ℤ)-1+legShift security core leg-intercept leg,
      rootLoad security layout core scalar (.inr (.inr leg))] slot
  | ⟨.inr (.inl center), _⟩ => rootLoad security layout core scalar (.inl center)
  | ⟨.inr (.inr queue), _⟩ => rootLoad security layout core scalar (.inr (.inl queue))

theorem at_natural (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (scalar : ℤ) (hcharge : publicCharge security core)
    (vertex : AssemblyIndex security) :
    rounding security (CurrentAffineGeometry.offset security layout core intercept scalar hcharge)
      (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
      AffineBaseline.offset (Parameters.modulus security) (centers security layout core)
        (legShift security core) intercept (placement security core) scalar
        (Sum.map (CurrentAffineGeometry.bodyEquiv security) id vertex) := by
  have hi : (dimensionEquiv security).symm
      (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
      relabeling security layout core (naturalNumbering security vertex) := by
    apply (dimensionEquiv security).injective
    rw [Equiv.apply_symm_apply, relabeling_natural]
  rw [offset_rounding security layout core 0 0 intercept scalar hcharge]
  unfold CurrentAffineLoad.load
  rw [show splitSource security (0 : Fin (Parameters.dimension security) → ℤ) = 0 from rfl]
  simp only [Prod.fst_zero, Prod.snd_zero, Matrix.mulVec_zero, map_zero, ZeroMemClass.coe_zero,
    zero_smul, zero_add, numberedOffset, hi, Equiv.symm_apply_apply, naturalNumbering,
    Equiv.trans_apply, Equiv.sumCongr_apply]
  rfl

theorem at_physical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (scalar : ℤ) (hcharge : publicCharge security core)
    (point : Sigma (Slots security)) :
    rounding security (CurrentAffineGeometry.offset security layout core intercept scalar hcharge)
      (core.endpointPermutation.symm (CurrentPhysicalNumbering.numbering security point)) =
      physical security layout core intercept scalar point := by
  have hp : CurrentPhysicalNumbering.numbering security point =
      endpointFlatten security layout (toAssembly security layout point) := by
    change PublicCoefficientOutput.flatten security point =
      PublicCoefficientOutput.flatten security (toPhysical security layout (toAssembly security layout point))
    rw [toPhysical_toAssembly]
  rw [hp, at_natural]
  rcases point with ⟨leg | (center | queue), slot⟩
  · change Fin 3 at slot
    fin_cases slot <;>
      simp [toAssembly, Fin.cases, Fin.induction, Fin.induction.go, AffineBaseline.offset,
        baseline, centers, placement, physical, rootLoad]
  · simp [toAssembly, AffineBaseline.offset, baseline, centers, placement, physical, rootLoad]
  · simp [toAssembly, AffineBaseline.offset, baseline, centers, placement, physical, rootLoad]

end
end CurrentAFT.CurrentOffsetPhysicalLoad

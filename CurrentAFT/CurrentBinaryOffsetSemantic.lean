import CurrentAFT.CurrentBinaryLoadSemantic
import CurrentAFT.CurrentOffsetPhysicalLoad

/-! The executed baseline and closure array is the actual offset's
rounding load, using the same stored core, placement and public shift. -/
namespace CurrentAFT.CurrentBinaryOffsetSemantic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentBinaryLoadColumns CurrentEmissionMetadata CurrentBinaryLoadSemantic
  CurrentAffineGeometry CurrentAffineLoad
open CurrentCoreProposal (MaterializedCore)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentEmissionMetadata.current CurrentProposalDimensions.current

theorem closure_eq (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (scalar : ℤ) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    AffineBaseline.closure (current security).bodyEdges scalar
      (((CurrentEmissionRootOrder.positions security layout core).value.get
        ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1)).cast
          (current_counts security).1.symm) =
    AffineBaseline.closure (bodyEdges security) scalar
      (CurrentAffineGeometry.bodyEquiv security
        (core.core.bodyPermutation.symm (layout.layout (CurrentBinaryBaselines.role security point)))) := by
  simp only [AffineBaseline.closure, Fin.ext_iff, Fin.val_cast, Fin.val_last, Fin.val_zero,
    root_position_value, (current_values security).1]
  rfl

theorem physicalLoad_eq (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (intercept : Fin (Legs security) → ℤ) (scalar : ℤ) (hcharge : publicCharge security core.core)
    (point : Point security) :
    CurrentBinaryOffsetLoad.physicalLoad security core layout.layout (Parameters.modulus security)
      (fun leg => legShift security core.core (CurrentEmissionMetadata.legEquiv security leg)) intercept
      (CurrentEmissionRootOrder.positions security layout core).value scalar point =
      rounding security
        (CurrentAffineGeometry.offset security layout.layout core.core
          (fun leg => intercept ((CurrentEmissionMetadata.legEquiv security).symm leg)) scalar hcharge)
        (core.core.endpointPermutation.symm (CurrentPhysicalNumbering.numbering security (pointEquiv security point))) := by
  rw [CurrentOffsetPhysicalLoad.at_physical]
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    fin_cases slot <;> simp only [pointEquiv, Equiv.coe_fn_mk, CurrentOffsetPhysicalLoad.physical,
      CurrentBinaryOffsetLoad.physicalLoad, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Equiv.symm_apply_apply, closure_eq, CurrentOffsetPhysicalLoad.rootLoad, CurrentBinaryBaselines.role]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    all_goals simp only [pointEquiv, Equiv.coe_fn_mk, CurrentOffsetPhysicalLoad.physical,
      CurrentBinaryOffsetLoad.physicalLoad, ← he, Equiv.symm_apply_apply, closure_eq,
      CurrentOffsetPhysicalLoad.rootLoad, CurrentBinaryBaselines.role]

end
end CurrentAFT.CurrentBinaryOffsetSemantic

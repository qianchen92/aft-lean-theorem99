import CurrentAFT.PointFamilyProducts
import CurrentAFT.RootIndependentSelectedPhysical
import CurrentAFT.FullResponsePointFormula

/-! The empty root component reconstructs the original canonical kernel
as coefficient data. No injectivity of physical evaluation is used. -/
namespace CurrentAFT.EmptyRootCoefficientIdentity
open AFT ControlCoordinates ControlProduct CanonicalReconstruction GradedControlAlgebra BackgroundFamilies
  LocalCoefficientFamily ProposalPrimary ActualControls CompleteRaising CompleteRaisingEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference

theorem emptyPointProduct (security order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → ActualControls.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    selectedPointProduct security order horder ∅ colors centers =
      Pi.single arity (pointKernel (primaryLaw security) (bodyReference security)
        (primaryReference_positive security) (bodyReference_positive security) colors centers) := by
  simp only [selectedPointProduct, Finset.notMem_empty, if_false, slotLeading, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  change (∏ index, primaryFamily (primaryLaw security) (bodyReference security) order horder
    (Hoeffding.centeredAtom (primaryLaw security) (colors index)) _)*
    (∏ index, bodyFamily (primaryLaw security) (bodyReference security) order horder
      (Hoeffding.centeredAtom (bodyReference security) (centers index)) _) = _
  exact PointFamilyProducts.two_pool_prod (primaryLaw security) (bodyReference security)
    (primaryReference_positive security) (bodyReference_positive security) order horder arity.property colors centers

theorem emptyCorrection (security order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val) :
    selectedCorrection security order horder ∅ kernel = Pi.single arity kernel := by
  unfold selectedCorrection
  simp_rw [emptyPointProduct security order horder arity]
  funext output
  by_cases he : output=arity
  · subst output
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]
    exact pointKernel_expansion (primaryLaw security) (bodyReference security)
      (primaryReference_positive security) (bodyReference_positive security) kernel
  · simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_eq_of_ne he, smul_zero, Finset.sum_const_zero]

theorem raising_single (security order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val) :
    raisingLinear security order horder (Pi.single arity kernel) =
      homogeneousCorrectionLinear security order horder arity.val.1.val arity.val.2.val kernel := by
  change (∑ index : TruncatedArity order, homogeneousCorrectionLinear security order horder
    index.val.1.val index.val.2.val ((Pi.single arity kernel : Family security order) index)) = _
  rw [Finset.sum_eq_single arity]
  · rw [Pi.single_eq_same]
  · intro index _ hne
    rw [Pi.single_eq_of_ne hne, map_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ arity)).elim

theorem normalized_single (security order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val) :
    normalizedJoint security order horder kernel =
      Pi.single arity kernel+raisingLinear security order horder (Pi.single arity kernel) := by
  rw [normalizedJoint_eq, emptyCorrection security order horder arity, raising_single]

theorem response_empty (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ) (arity : TruncatedArity order)
    (selection : TaggedSelection.Selection security arity.val.1.val arity.val.2.val)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val) :
    ActualRootResponse.response order horder queue selection ∅ layout kernel =
      Pi.single arity kernel+raisingLinear security order horder (Pi.single arity kernel) := by
  rw [RootIndependentSelectedPhysical.response_empty, normalized_single security order horder arity]

end
end CurrentAFT.EmptyRootCoefficientIdentity

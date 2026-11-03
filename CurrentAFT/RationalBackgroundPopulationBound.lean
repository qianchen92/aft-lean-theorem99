import CurrentAFT.NumericalPopulationConstants

/-! # A polynomial point bound for the actual complete fixed-queue data -/
namespace CurrentAFT.RationalBackgroundPopulationProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  ProposalPrimary.primaryLaw bodyReference

def bound (security order : ℕ) : ℝ :=
  (Fintype.card (TruncatedArity order):ℝ)^2*(freeQueueBound security order*legBound security order)

theorem bound_nonneg (security order : ℕ) : 0≤bound security order := by
  rcases constants_nonneg security order with ⟨hf,hq,hl,_,_,_⟩
  unfold bound freeQueueBound
  positivity

theorem actual_bound (security order : ℕ) (horder : 2≤order) (queue : ℤ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(ActualBackground.fixedQueueBackground security order horder queue arity).val colors centers|≤bound security order := by
  rcases constants_nonneg security order with ⟨hf,hq,hl,_,_,_⟩
  have hFQ : ∀ arity colors centers,
      |data security order (familyProduct (ProposalPrimary.primaryLaw security) (bodyReference security) order
        (freeActual security order horder) (queueActual security order horder queue)) arity colors centers|≤freeQueueBound security order := by
    intro arity colors centers
    rw [← data_product]
    exact (RationalFamilyProductProgram.product_bound order _ _ _ _ hf hq (free_bound security order horder)
      (queue_bound security order horder queue) arity colors centers).trans_eq (by unfold freeQueueBound; ring)
  have hFQ0 : 0≤freeQueueBound security order := by unfold freeQueueBound; positivity
  change |data security order (familyProduct (ProposalPrimary.primaryLaw security) (bodyReference security) order
    (familyProduct (ProposalPrimary.primaryLaw security) (bodyReference security) order
      (freeActual security order horder) (queueActual security order horder queue))
    (legActual security order horder)) arity colors centers|≤_
  rw [← data_product]
  exact RationalFamilyProductProgram.product_bound order _ _ _ _ hFQ0 hl hFQ (leg_bound security order horder) arity colors centers

end
end CurrentAFT.RationalBackgroundPopulationProgram

namespace CurrentAFT.NumericalPopulationConstants
open AFT PolynomialErrorEnvelope
noncomputable section

theorem actual_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.bound security order) := by
  have h := (PolynomialErrorEnvelope.constant ((Fintype.card (GradedControlAlgebra.TruncatedArity order):ℝ)^2)).mul
    ((((PolynomialErrorEnvelope.constant ((Fintype.card (GradedControlAlgebra.TruncatedArity order):ℝ)^2)).mul
      (free_bound order)).mul (queue_bound order)).mul (leg_bound order))
  exact h

end
end CurrentAFT.NumericalPopulationConstants

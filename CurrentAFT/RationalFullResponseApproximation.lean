import CurrentAFT.RationalFullResponseAverages
import CurrentAFT.RationalBackgroundPopulationBound

/-! Uniform error for the full response with its one shared queue. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension primaryLaw bodyReference

def fixedQueueBound (security order : ℕ) : ℝ :=
  (Fintype.card (TruncatedArity order):ℝ)^2*RationalBackgroundPopulationProgram.bound security order*rootBound security order

def fixedQueueError (security order : ℕ) : ℝ :=
  productError order (RationalBackgroundPopulationProgram.bound security order) (rootBound security order)
    (RationalBackgroundPopulationProgram.errorConstant security order) (rootError security order)

def responseError (security order : ℕ) : ℝ := fixedQueueError security order+fixedQueueBound security order

def errorConstant (security order : ℕ) : ℝ := responseError security order+RationalPackedRootProgram.kernelErrorBound security order

theorem constants_nonneg (security order : ℕ) :
    0 ≤ rootBound security order ∧ 0 ≤ rootError security order ∧
    0 ≤ fixedQueueBound security order ∧ 0 ≤ fixedQueueError security order ∧
    0 ≤ responseError security order ∧ 0 ≤ errorConstant security order := by
  have ht : 0 ≤ tagCountBound security order := by unfold tagCountBound; positivity
  have hb : 0 ≤ rootBound security order := mul_nonneg ht (RationalPackedRootProgram.responseBound_nonneg security order)
  have he : 0 ≤ rootError security order := mul_nonneg ht (RationalPackedRootProgram.errorConstant_nonneg security order)
  have hfB := RationalBackgroundPopulationProgram.bound_nonneg security order
  have hfE := RationalBackgroundPopulationProgram.errorConstant_nonneg security order
  have hB : 0 ≤ fixedQueueBound security order := by unfold fixedQueueBound; positivity
  have hE : 0 ≤ fixedQueueError security order := productError_nonneg _ _ _ _ _ hfB hb hfE he
  have hR : 0 ≤ responseError security order := add_nonneg hE hB
  exact ⟨hb, he, hB, hE, hR, add_nonneg hR (RationalPackedRootProgram.kernelErrorBound_nonneg security order)⟩

theorem fixedQueue_bound (security order : ℕ) (horder : 2 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order (FullResponseWeightedIdentity.fixedQueue security order horder hroom queue source layout)
      arity colors centers| ≤ fixedQueueBound security order := by
  change |data security order (familyProduct (primaryLaw security) (bodyReference security) order
    (ActualBackground.fixedQueueBackground security order horder queue)
    (FullResponseWeightedIdentity.choiceAverage security order (by omega) hroom queue source layout)) arity colors centers| ≤ _
  rw [← data_product]
  exact (RationalFamilyProductProgram.product_bound order _ _ _ _
    (RationalBackgroundPopulationProgram.bound_nonneg security order) (constants_nonneg security order).1
    (RationalBackgroundPopulationProgram.actual_bound security order horder queue)
    (choiceAverage_bound security order (by omega) hroom queue source layout) arity colors centers).trans_eq
      (by unfold fixedQueueBound; ring)

theorem fixedQueue_error (security bits order : ℕ) (horder : 2 ≤ order)
    (hroom : 2*order ≤ security) (hbody : order ≤ Parameters.bodySize security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (fixedQueue security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers-
      data security order (FullResponseWeightedIdentity.fixedQueue security order horder hroom queue source layout)
        arity colors centers| ≤ fixedQueueError security order*(1/(2:ℝ)^bits) := by
  exact product_error security bits order (ActualBackground.fixedQueueBackground security order horder queue)
    (FullResponseWeightedIdentity.choiceAverage security order (by omega) hroom queue source layout)
    (RationalBackgroundPopulationProgram.current security bits order queue)
    (choiceAverage security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val))
    _ _ _ _ (RationalBackgroundPopulationProgram.bound_nonneg security order) (constants_nonneg security order).1
    (RationalBackgroundPopulationProgram.errorConstant_nonneg security order) (constants_nonneg security order).2.1
    (RationalBackgroundPopulationProgram.actual_bound security order horder queue)
    (choiceAverage_bound security order (by omega) hroom queue source layout)
    (RationalBackgroundPopulationProgram.current_error security bits order horder queue hfirst hprecision hbudget)
    (choiceAverage_error security bits order (by omega) hroom hbody queue source layout hfirst hprecision hbudget)
    arity colors centers

theorem response_error (security bits order : ℕ) (horder : 2 ≤ order)
    (hroom : 2*order ≤ security) (hbody : order ≤ Parameters.bodySize security)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (response security bits order source.1.val.1.val source.1.val.2.val
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers-
      data security order (FullResponseWeightedIdentity.response security order horder hroom source layout)
        arity colors centers| ≤ responseError security order*(1/(2:ℝ)^bits) := by
  exact RationalScalarFamilyAverage.current_error security bits order
    (fun scalar => FullResponseWeightedIdentity.fixedQueue security order horder hroom scalar.val source layout)
    (fun queue => fixedQueue security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val))
    _ _ (constants_nonneg security order).2.2.1
    (fun scalar => fixedQueue_bound security order horder hroom scalar.val source layout)
    (fun scalar => fixedQueue_error security bits order horder hroom hbody scalar.val source layout hfirst hprecision hbudget)
    arity colors centers

theorem basis_error (security bits order : ℕ) (source : Index security order)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (basis security bits order source.1
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers-
      data security order (Pi.single source.1 (FullResponseWeightedIdentity.sourceKernel security order source))
        arity colors centers| ≤ RationalPackedRootProgram.kernelErrorBound security order*(1/(2:ℝ)^bits) := by
  by_cases he : arity=source.1
  · subst arity
    simp only [interpret, RationalFamilyProductProgram.pullback, RationalFamilyProductProgram.realTable,
      basis, Fin.cast_refl, data, Pi.single_eq_same, FullResponseWeightedIdentity.sourceKernel]
    exact (WeightedPointKernelProgram.current_error security bits _ _ source.2.1 source.2.2 hprecision hbudget colors centers).trans
      (mul_le_mul_of_nonneg_right (RationalPackedRootProgram.pointKernelError_le security order _ _ source.1.property) (by positivity))
  · simp only [interpret, RationalFamilyProductProgram.pullback, RationalFamilyProductProgram.realTable,
      basis, dif_neg he, data, Pi.single_eq_of_ne he, Submodule.coe_zero, Pi.zero_apply, Rat.cast_zero, sub_zero, abs_zero]
    exact mul_nonneg (RationalPackedRootProgram.kernelErrorBound_nonneg security order) (by positivity)

end
end CurrentAFT.RationalFullResponseProgram

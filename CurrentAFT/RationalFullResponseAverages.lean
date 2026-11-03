import CurrentAFT.FullResponseWeightedIdentity
import CurrentAFT.RationalPackedRootBound

/-! Uniform approximation bounds through bounded tag sums and the actual
two-pool without-replacement average. No number of choices multiplies error. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  UniformTaggedOutput ActualRootFamily FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference

def tagCountBound (security order : ℕ) : ℝ := 1+(order+1)*(Parameters.bodySize security:ℝ)^order
def rootBound (security order : ℕ) : ℝ := tagCountBound security order*RationalPackedRootProgram.responseBound security order
def rootError (security order : ℕ) : ℝ := tagCountBound security order*RationalPackedRootProgram.errorConstant security order

theorem tags_card (security order : ℕ) : 1+((tags security order).card:ℝ) ≤ tagCountBound security order := by
  have hb : 1 ≤ Fintype.card (BlockIndex security) := by
    rw [FullResponseEnumeration.block_card]
    have h := CycleRootExpansion.current_body_two_le security
    omega
  have h := (Finset.card_filter_le (s := FullResponseEnumeration.boundedSubsets (BlockIndex security) order)
    (p := fun tagged => 2 ≤ tagged.card)).trans (FullResponseEnumeration.boundedSubsets_card order hb)
  rw [FullResponseEnumeration.block_card] at h
  unfold tagCountBound tags
  exact_mod_cast Nat.add_le_add_left h 1

theorem tags_degree {security order : ℕ} {tagged : Finset (BlockIndex security)} (h : tagged ∈ tags security order) :
    tagged.card ≤ order := (FullResponseEnumeration.mem_boundedSubsets order tagged).mp (Finset.mem_filter.mp h).1

theorem scalar_add_sum_bound {Index : Type*} (indices : Finset Index) (first : ℝ) (terms : Index → ℝ)
    (bound : ℝ) (hfirst : |first| ≤ bound) (hterms : ∀ index ∈ indices, |terms index| ≤ bound) :
    |first+∑ index ∈ indices, terms index| ≤ (1+(indices.card:ℝ))*bound := by
  have hs := (Finset.abs_sum_le_sum_abs terms indices).trans (Finset.sum_le_sum hterms)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  exact (abs_add_le _ _).trans ((add_le_add hfirst hs).trans_eq (by ring))

theorem selected_bound (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (source : Index security order) (chosen : Selection security source.1.val.1.val source.1.val.2.val)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order (FullResponseWeightedIdentity.selected security order horder queue source chosen layout)
      arity colors centers| ≤ rootBound security order := by
  have ht (tagged : Finset (BlockIndex security)) (htags : tagged.card ≤ order) :=
    RationalPackedRootProgram.response_actual_bound order horder queue chosen tagged layout source.1.property htags
      source.2.1 source.2.2 arity colors centers
  have h := scalar_add_sum_bound (tags security order) _ _ (RationalPackedRootProgram.responseBound security order)
    (ht ∅ (by simp)) (fun tagged hm => ht tagged (tags_degree hm))
  simp only [data, FullResponseWeightedIdentity.selected, Pi.add_apply, Submodule.coe_add,
    Finset.sum_apply, Submodule.coe_sum, FullResponseWeightedIdentity.sourceKernel] at *
  exact h.trans (mul_le_mul_of_nonneg_right (tags_card security order)
    (RationalPackedRootProgram.responseBound_nonneg security order))

theorem selected_error (security bits order : ℕ) (horder : 1 ≤ order) (hroom : order ≤ Parameters.bodySize security) (queue : ℤ)
    (source : Index security order) (chosen : Selection security source.1.val.1.val source.1.val.2.val)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (selected bits order queue chosen (fun index => (source.2.1 index).val)
      (fun index => (source.2.2 index).val.val)) arity colors centers-
      data security order (FullResponseWeightedIdentity.selected security order horder queue source chosen layout)
        arity colors centers| ≤ rootError security order*(1/(2:ℝ)^bits) := by
  have ht (tagged : Finset (BlockIndex security)) (htags : tagged.card ≤ order) :=
    RationalPackedRootProgram.current_error bits order horder queue chosen tagged layout (htags.trans hroom)
      source.1.property htags source.2.1 source.2.2 hfirst hprecision hbudget arity colors centers
  have h := scalar_add_sum_bound (tags security order) _ _
    (RationalPackedRootProgram.errorConstant security order*(1/(2:ℝ)^bits))
    (ht ∅ (by simp)) (fun tagged hm => ht tagged (tags_degree hm))
  simp only [interpret, RationalFamilyProductProgram.pullback, RationalFamilyProductProgram.realTable,
    selected, Rat.cast_add, Rat.cast_sum, data, FullResponseWeightedIdentity.selected,
    Pi.add_apply, Submodule.coe_add, Finset.sum_apply, Submodule.coe_sum, FullResponseWeightedIdentity.sourceKernel] at *
  rw [Finset.sum_sub_distrib] at h
  have h' := h.trans (mul_le_mul_of_nonneg_right (tags_card security order)
    (mul_nonneg (RationalPackedRootProgram.errorConstant_nonneg security order) (by positivity)))
  convert h' using 1
  · congr 1
    ring
  · unfold rootError
    ring

theorem choiceAverage_cast (security bits order : ℕ) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : Index security order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    interpret security order (choiceAverage security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers =
    (choiceLaw security _ _ (primary_room security order hroom source.1) (body_room security order hroom source.1)).expectation
      (fun choice => interpret security order (selected bits order queue (UniformTaggedOutput.selection security _ _ choice)
        (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers) := by
  unfold interpret RationalFamilyProductProgram.pullback RationalFamilyProductProgram.realTable choiceAverage
  simp only [Rat.cast_div, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, FiniteDist.expectation,
    choiceLaw_weight, Finset.sum_div, one_div, selection_eq]
  apply Finset.sum_congr (by ext choice; simp)
  intro choice _
  ring

theorem choiceAverage_data (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    data security order (FullResponseWeightedIdentity.choiceAverage security order horder hroom queue source layout) arity colors centers =
    (choiceLaw security _ _ (primary_room security order hroom source.1) (body_room security order hroom source.1)).expectation
      (fun choice => data security order (FullResponseWeightedIdentity.selected security order horder queue source
        (UniformTaggedOutput.selection security _ _ choice) layout) arity colors centers) := by
  simp only [data, FullResponseWeightedIdentity.choiceAverage, FiniteDist.expectation, Finset.sum_apply,
    Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]

theorem choiceAverage_bound (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order (FullResponseWeightedIdentity.choiceAverage security order horder hroom queue source layout)
      arity colors centers| ≤ rootBound security order := by
  rw [choiceAverage_data]
  exact CalibrationCoordinateError.expectation_abs_bound _ _ _
    (fun choice => selected_bound security order horder queue source _ layout arity colors centers)

theorem choiceAverage_error (security bits order : ℕ) (horder : 1 ≤ order)
    (hroom : 2*order ≤ security) (hbody : order ≤ Parameters.bodySize security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (choiceAverage security bits order source.1.val.1.val source.1.val.2.val queue
      (fun index => (source.2.1 index).val) (fun index => (source.2.2 index).val.val)) arity colors centers-
      data security order (FullResponseWeightedIdentity.choiceAverage security order horder hroom queue source layout)
        arity colors centers| ≤ rootError security order*(1/(2:ℝ)^bits) := by
  rw [choiceAverage_cast security bits order hroom, choiceAverage_data, ← FiniteDist.expectation_sub]
  exact CalibrationCoordinateError.expectation_abs_bound _ _ _
    (fun choice => selected_error security bits order horder hbody queue source _ layout hfirst hprecision hbudget arity colors centers)

end
end CurrentAFT.RationalFullResponseProgram

import CurrentAFT.RationalPackedRootScalar
import CurrentAFT.RationalPackedRootProduct

/-! # The native rational joint sum approximates the actual response data -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  ControlCoordinates GradedControlAlgebra RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedApproxFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedApproxSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
local instance packedApproxSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance packedApproxSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

def sourceError (security order r s count tags : ℕ) : ℝ :=
  (scalarBound security r s tags * count * RationalRootGroupProgram.errorConstant security order +
    scalarError security r s count tags) * (localGrowth security order)^count

theorem sourceError_nonneg (security order r s count tags : ℕ) :
    0 ≤ sourceError security order r s count tags := by
  unfold sourceError
  have hs := scalarBound_nonneg security r s tags
  have he := scalarError_nonneg security r s count tags
  have hE := RationalRootGroupProgram.errorConstant_nonneg security order
  have hC := (by norm_num : (0:ℝ)≤1).trans (localGrowth_one_le security order)
  positivity

theorem source_error {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security) (hroom : tagged.card ≤ Parameters.bodySize security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (summand security bits order queue (actualMetadata selection tagged)
        (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)
        (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source))) arity colors centers -
      actualScalar selection tagged layout sourcePrimary sourceBody source *
        data security order (productActual order horder queue selection tagged source) arity colors centers| ≤
      sourceError security order r s (groupCount selection tagged) tagged.card*(1/(2:ℝ)^bits) := by
  let word := sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
  have hvalue : interpret security order (summand security bits order queue (actualMetadata selection tagged)
      (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val) word) arity colors centers =
      interpret security order (localProduct security bits order queue (actualMetadata selection tagged) word) arity colors centers *
        (sourceScalar bits selection tagged sourcePrimary sourceBody source:ℝ) := by
    unfold interpret RationalFamilyProductProgram.pullback RationalFamilyProductProgram.realTable summand
    rw [if_pos (valid_sourceIndex selection tagged source)]
    push_cast
    unfold sourceScalar
    push_cast
    ring
  rw [hvalue, mul_comm (actualScalar _ _ _ _ _ _)]
  have hC := (by norm_num : (0:ℝ)≤1).trans (localGrowth_one_le security order)
  have h := two_factor_error
    (interpret security order (localProduct security bits order queue (actualMetadata selection tagged) word) arity colors centers)
    (sourceScalar bits selection tagged sourcePrimary sourceBody source:ℝ)
    (data security order (productActual order horder queue selection tagged source) arity colors centers)
    (actualScalar selection tagged layout sourcePrimary sourceBody source)
    ((localGrowth security order)^(groupCount selection tagged)) (scalarBound security r s tagged.card)
    (localProductError security order (groupCount selection tagged)*(1/(2:ℝ)^bits))
    (scalarError security r s (groupCount selection tagged) tagged.card*(1/(2:ℝ)^bits))
    (by positivity) (scalarBound_nonneg security r s tagged.card) (by
      unfold localProductError
      have he := RationalRootGroupProgram.errorConstant_nonneg security order
      have hc := (by norm_num : (0:ℝ)≤1).trans (localGrowth_one_le security order)
      positivity) (mul_nonneg (scalarError_nonneg _ _ _ _ _) (by positivity))
    (productActual_bound order horder queue selection tagged source arity colors centers)
    (sourceScalar_bound bits selection tagged layout hroom sourcePrimary sourceBody source hprecision hbudget)
    (localProduct_error bits order horder queue selection tagged source hfirst hprecision hbudget arity colors centers)
    (scalar_error bits selection tagged layout hroom sourcePrimary sourceBody source hprecision hbudget)
  exact h.trans_eq (by unfold sourceError localProductError; ring)

def rawErrorConstant (security order r s count tags : ℕ) : ℝ :=
  (CurrentRectangleIndex.colors security : ℝ)^(count*3) * sourceError security order r s count tags

theorem current_error_raw {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security) (hroom : tagged.card ≤ Parameters.bodySize security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (current security bits order queue (actualMetadata selection tagged)
        (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)) arity colors centers -
      data security order (ActualRootResponse.response order horder queue selection tagged layout
        (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)) arity colors centers| ≤
      rawErrorConstant security order r s (groupCount selection tagged) tagged.card*(1/(2:ℝ)^bits) := by
  have hresponse : data security order (ActualRootResponse.response order horder queue selection tagged layout
      (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)) arity colors centers =
      ∑ index : Fin ((CurrentRectangleIndex.colors security)^((groupCount selection tagged)*3)),
        (CurrentGroupSourcePadding.decode selection tagged (CurrentRootOrdering.keptOrdering selection tagged) index).elim 0
          (fun source => actualScalar selection tagged layout sourcePrimary sourceBody source *
            data security order (productActual order horder queue selection tagged source) arity colors centers) := by
    rw [CurrentGroupSourcePadding.response_eq order horder queue selection tagged (CurrentRootOrdering.keptOrdering selection tagged)]
    simp only [data, Finset.sum_apply, Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro index _
    cases CurrentGroupSourcePadding.decode selection tagged (CurrentRootOrdering.keptOrdering selection tagged) index with
    | none => rfl
    | some source =>
      simp only [Option.elim_some, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul]
      have hp : (∏ group, RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group)) =
          productActual order horder queue selection tagged source := by
        unfold productActual
        apply Finset.prod_congr (by ext; simp)
        intro group _
        rfl
      rw [hp]
      rfl
  have hcomputed : interpret security order (current security bits order queue (actualMetadata selection tagged)
      (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)) arity colors centers =
      ∑ index : Fin ((CurrentRectangleIndex.colors security)^((groupCount selection tagged)*3)),
        interpret security order (summand security bits order queue (actualMetadata selection tagged)
          (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)
          (sourceWord security (groupCount selection tagged) index)) arity colors centers := by
    simp only [interpret, RationalFamilyProductProgram.pullback, RationalFamilyProductProgram.realTable, current, Rat.cast_sum]
    rfl
  rw [hcomputed, hresponse, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _index : Fin ((CurrentRectangleIndex.colors security)^((groupCount selection tagged)*3)),
        sourceError security order r s (groupCount selection tagged) tagged.card*(1/(2:ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro index _
      cases hd : CurrentGroupSourcePadding.decode selection tagged (CurrentRootOrdering.keptOrdering selection tagged) index with
      | none =>
        have hv := (decode_none_iff selection tagged index).mp hd
        simp only [Option.elim_none, interpret, RationalFamilyProductProgram.pullback,
          RationalFamilyProductProgram.realTable, summand, hv, ite_false, Rat.cast_zero, sub_zero, abs_zero]
        exact mul_nonneg (sourceError_nonneg _ _ _ _ _ _) (by positivity)
      | some source =>
        have hi := (decode_eq_some selection tagged index source).mp hd
        subst index
        exact source_error bits order horder queue selection tagged layout hroom sourcePrimary sourceBody source
          hfirst hprecision hbudget arity colors centers
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, rawErrorConstant]; ring

end
end CurrentAFT.RationalPackedRootProgram

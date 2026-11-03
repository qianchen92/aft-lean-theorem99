import CurrentAFT.RationalPackedRootSource
import CurrentAFT.RationalRootGroupBounds

/-! # The packed product preserves every actual local factor and its joint source -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRectangleIndex RationalRootGroupProgram CycleRootExpansion ActualControls
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedProductFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def productActual {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) : BackgroundFamilies.ActualFamily security order :=
  ∏ group, RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group)

theorem localProduct_interpret {security r s : ℕ} (bits order : ℕ) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) :
    interpret security order (localProduct security bits order queue (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source))) =
      RationalFamilyWordProduct.current order (groupCount selection tagged) (fun index =>
        interpret security order (RationalRootGroupProgram.table bits order queue selection tagged
          (ordering selection tagged index) (source (ordering selection tagged index)))) := by
  have ht : (fun index => localTable security bits order queue ((actualMetadata selection tagged).roles index)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source) index)) =
      fun index => RationalRootGroupProgram.table bits order queue selection tagged
        (ordering selection tagged index) (source (ordering selection tagged index)) := by
    funext index
    rw [sourceWord_sourceIndex]
    rfl
  unfold localProduct
  rw [ht, RationalFamilyWordProduct.interpret_current]
  rfl

theorem orderedProduct_actual {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) :
    RationalFamilyWordProduct.current order (groupCount selection tagged) (fun index => data security order
      (RootReferenceColumns.reducedColumn order horder queue selection tagged
        (ordering selection tagged index) (source (ordering selection tagged index)))) =
      data security order (productActual order horder queue selection tagged source) := by
  unfold data
  rw [RationalFamilyWordProduct.current_actual]
  have hp := (ordering selection tagged).prod_comp (fun group =>
    RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group))
  exact congrArg (fun family : BackgroundFamilies.ActualFamily security order =>
    fun arity => (family arity).val) hp

def localGrowth (security order : ℕ) : ℝ :=
  growth order (RationalRootGroupProgram.pointBound security order) (RationalRootGroupProgram.errorConstant security order)

theorem localGrowth_one_le (security order : ℕ) : 1 ≤ localGrowth security order :=
  growth_ge_one _ _ _ ((by norm_num : (0 : ℝ) ≤ 1).trans (RationalRootGroupProgram.pointBound_one_le security order))
    (RationalRootGroupProgram.errorConstant_nonneg security order)

def localProductError (security order count : ℕ) : ℝ :=
  count * RationalRootGroupProgram.errorConstant security order * (localGrowth security order)^count

theorem localProduct_error {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (localProduct security bits order queue (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source))) arity colors centers -
      data security order (productActual order horder queue selection tagged source) arity colors centers| ≤
      localProductError security order (groupCount selection tagged) * (1 / (2 : ℝ)^bits) := by
  let A := RationalRootGroupProgram.pointBound security order
  let E := RationalRootGroupProgram.errorConstant security order
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (RationalRootGroupProgram.pointBound_one_le security order)
  have hE : 0 ≤ E := RationalRootGroupProgram.errorConstant_nonneg security order
  have he : 0 ≤ epsilon := by positivity
  have hsmall : E * epsilon ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (RationalCoefficientExtraction.epsilon_le_one bits) hE
  have hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * (A + E*epsilon + 1) ≤ localGrowth security order := by
    apply le_trans _ (growth_scale order A E)
    gcongr
  have h := RationalFamilyWordProduct.current_error order (groupCount selection tagged)
    (fun index => data security order (RootReferenceColumns.reducedColumn order horder queue selection tagged
      (ordering selection tagged index) (source (ordering selection tagged index))))
    (fun index => interpret security order (RationalRootGroupProgram.table bits order queue selection tagged
      (ordering selection tagged index) (source (ordering selection tagged index))))
    A (E*epsilon) (localGrowth security order) hA (by positivity) (localGrowth_one_le security order) hscale
    (fun index => RationalRootGroupProgram.local_bound order horder queue selection tagged _ _)
    (fun index => RationalRootGroupProgram.local_error bits order horder queue selection tagged _ _ hfirst hprecision hbudget)
    arity colors centers
  rw [← localProduct_interpret, orderedProduct_actual] at h
  exact h.trans_eq (by unfold localProductError; dsimp only [E, epsilon]; ring)

theorem productActual_bound {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order (productActual order horder queue selection tagged source) arity colors centers| ≤
      (localGrowth security order)^(groupCount selection tagged) := by
  let A := RationalRootGroupProgram.pointBound security order
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (RationalRootGroupProgram.pointBound_one_le security order)
  have hscale : (Nat.card (TruncatedArity order) : ℝ)^2 * A ≤ localGrowth security order := by
    apply le_trans _ (growth_scale order A (RationalRootGroupProgram.errorConstant security order))
    gcongr
    have hE := RationalRootGroupProgram.errorConstant_nonneg security order
    linarith
  have h := RationalFamilyWordProduct.current_bound order (groupCount selection tagged)
    (fun index => data security order (RootReferenceColumns.reducedColumn order horder queue selection tagged
      (ordering selection tagged index) (source (ordering selection tagged index)))) A (localGrowth security order)
    hA (localGrowth_one_le security order) hscale
    (fun index => RationalRootGroupProgram.local_bound order horder queue selection tagged _ _) arity colors centers
  rw [orderedProduct_actual] at h
  exact h

end
end CurrentAFT.RationalPackedRootProgram

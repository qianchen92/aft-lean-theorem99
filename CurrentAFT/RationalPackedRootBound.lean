import CurrentAFT.RationalPackedRootRates

/-! # An actual point bound for the full packed joint response -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  GradedControlAlgebra RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedBoundFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedBoundSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
local instance packedBoundSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance packedBoundSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

def responseBound (security order : ℕ) : ℝ :=
  (CurrentRectangleIndex.colors security:ℝ)^(6*order)*(localGrowth security order)^(2*order)

theorem responseBound_nonneg (security order : ℕ) : 0 ≤ responseBound security order := by
  unfold responseBound
  have hc := (by norm_num : (0:ℝ)≤1).trans (localGrowth_one_le security order)
  positivity

theorem actualScalar_bound {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged) :
    |actualScalar selection tagged layout sourcePrimary sourceBody source|≤1 := by
  have hc := control_bound selection tagged sourcePrimary sourceBody source
  have hu := untaggedWeight_bounds selection tagged source
  have hw := weightedCoefficient_bound selection tagged layout source
  unfold actualScalar
  rw [abs_mul, abs_mul, abs_of_nonneg hu.1]
  exact (mul_le_mul (mul_le_mul hc hu.2 hu.1 (by norm_num)) hw (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem response_actual_bound {security r s : ℕ} (order : ℕ) (horder : 1≤order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security) (hdegree : r+s≤order) (htags : tagged.card≤order)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order (ActualRootResponse.response order horder queue selection tagged layout
      (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)) arity colors centers| ≤
      responseBound security order := by
  have hc := localGrowth_one_le security order
  have hcn := (by norm_num : (0:ℝ)≤1).trans hc
  have hcount : groupCount selection tagged≤2*order := by
    have hk := CurrentRootOrdering.kept_count_le selection tagged
    unfold groupCount
    omega
  rw [CurrentGroupSourcePadding.response_eq order horder queue selection tagged (CurrentRootOrdering.keptOrdering selection tagged)]
  simp only [data, Finset.sum_apply, Submodule.coe_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _index : Fin ((CurrentRectangleIndex.colors security)^((groupCount selection tagged)*3)),
        (localGrowth security order)^(groupCount selection tagged) := by
      apply Finset.sum_le_sum
      intro index _
      cases CurrentGroupSourcePadding.decode selection tagged (CurrentRootOrdering.keptOrdering selection tagged) index with
      | none => simpa only [Option.elim_none, Pi.zero_apply, Submodule.coe_zero, abs_zero] using pow_nonneg hcn (groupCount selection tagged)
      | some source =>
        simp only [Option.elim_some, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul]
        have hp : (∏ group, RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group)) =
            productActual order horder queue selection tagged source := by
          unfold productActual
          apply Finset.prod_congr (by ext; simp)
          intro group _
          rfl
        rw [hp, abs_mul]
        exact (mul_le_mul (actualScalar_bound selection tagged layout sourcePrimary sourceBody source)
          (productActual_bound order horder queue selection tagged source arity colors centers)
          (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = (CurrentRectangleIndex.colors security:ℝ)^((groupCount selection tagged)*3)*
        (localGrowth security order)^(groupCount selection tagged) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    _ ≤ responseBound security order := by
      unfold responseBound
      have hq : (1:ℝ)≤CurrentRectangleIndex.colors security := by exact_mod_cast CurrentRectangleIndex.colors_pos security
      exact mul_le_mul (pow_le_pow_right₀ hq (by omega)) (pow_le_pow_right₀ hc hcount)
        (pow_nonneg hcn _) (by positivity)

theorem responseBound_polynomial (order : ℕ) : PolynomialErrorEnvelope (fun security => responseBound security order) := by
  have hp := NumericalGroupConstants.error order
  have hb := NumericalGroupConstants.point_bound order
  simp only [responseBound, localGrowth, RationalFamilyProductProgram.growth, CurrentRectangleIndex.colors_eq]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow

end
end CurrentAFT.RationalPackedRootProgram

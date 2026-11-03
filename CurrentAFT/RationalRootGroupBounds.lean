import CurrentAFT.RationalRootGroupProgram

/-! # Actual point bounds for every reduced local root column -/
namespace CurrentAFT.RationalRootGroupProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance groupBoundsFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance groupBoundsSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference

def primaryBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  (LocalCoefficientPointBounds.numeratorBound security * RationalNormalizedPrimaryProgram.inverseBound security order)

theorem primary_bound (security order : ℕ) (roots : RootTaggedSelected.RootPair security) (source : Palette security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.primaryAt security order roots source arity).val colors centers| ≤ primaryBound security order := by
  let numerator := LocalRaisingLinear.completeFamilyLinear security order
    (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single source 1)))
  have h := product_bound order (data security order numerator) (data security order (LocalRaisingBounds.positiveInverse security order))
    (LocalCoefficientPointBounds.numeratorBound security) (RationalNormalizedPrimaryProgram.inverseBound security order)
    (LocalCoefficientPointBounds.numeratorBound_nonneg security) (RationalNormalizedPrimaryProgram.inverseBound_nonneg security order)
    (LocalCoefficientPointBounds.numerator_bound security order roots source) (RationalNormalizedPrimaryProgram.actual_inverse_bound security order)
    arity colors centers
  rw [data_product] at h
  exact h

def ordinaryBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  RationalSingletonProgram.inverseBound security order + 2 * RationalOrdinaryFamilyProgram.atRootBound security order

theorem independent_bound (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers| ≤
      (Fintype.card (TruncatedArity order) : ℝ)^2 * RationalSingletonProgram.inverseBound security order := by
  have h := product_bound order
    (data security order (RaisingChannels.bodyLeading security order horder (Pi.single source 1)))
    (data security order (OrdinaryRaising.positiveInverse security order horder))
    1 (RationalSingletonProgram.inverseBound security order) (by norm_num)
    (RationalOrdinaryFamilyProgram.inverse_constants_nonneg security order).1
    (RationalOrdinaryFamilyProgram.actual_body_bound security order horder source)
    (RationalOrdinaryFamilyProgram.actual_inverse_bound security order horder) arity colors centers
  rw [data_product] at h
  simpa only [one_mul] using h

theorem ordinary_bound (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.hybridAt security order horder root (Pi.single source 1) arity).val colors centers| ≤ ordinaryBound security order := by
  have hmean : |∑ other : Root security, (rootReference security).weight other *
      (RootReferenceColumns.ordinaryAt security order horder other (Pi.single source 1) arity).val colors centers| ≤
      RationalOrdinaryFamilyProgram.atRootBound security order := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ other : Root security, (rootReference security).weight other * RationalOrdinaryFamilyProgram.atRootBound security order := by
        apply Finset.sum_le_sum
        intro other _
        rw [abs_mul, abs_of_nonneg ((rootReference security).nonneg other)]
        exact mul_le_mul_of_nonneg_left
          (RationalOrdinaryFamilyProgram.actual_atRoot_bound security order horder source other arity colors centers)
          ((rootReference security).nonneg other)
      _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  simp only [RootReferenceColumns.hybridAt, Pi.sub_apply, Pi.add_apply, Submodule.coe_sub, Submodule.coe_add,
    Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact (abs_sub _ _).trans ((add_le_add
    ((abs_add_le _ _).trans (add_le_add (independent_bound security order horder source arity colors centers)
      (RationalOrdinaryFamilyProgram.actual_atRoot_bound security order horder source root arity colors centers))) hmean).trans_eq
      (by unfold ordinaryBound; ring))

def legBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  (RationalUnselectedLegProgram.numeratorBound security * RationalUnselectedLegProgram.inverseBound security order)

theorem leg_bound (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.legAt security order horder root arity).val colors centers| ≤ legBound security order := by
  have h := product_bound order (data security order (RationalUnselectedLegProgram.numeratorActual security order horder root))
    (data security order (RootLegReciprocal.reciprocal security order))
    (RationalUnselectedLegProgram.numeratorBound security) (RationalUnselectedLegProgram.inverseBound security order)
    (RationalUnselectedLegProgram.numerator_constants_nonneg security).1 (RationalUnselectedLegProgram.inverse_constants_nonneg security order).1
    (RationalUnselectedLegProgram.actual_numerator_bound security order horder root)
    (RationalUnselectedLegProgram.actual_inverse_bound security order) arity colors centers
  rw [data_product] at h
  exact h

def singletonBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  (RationalSingletonProgram.firstBound security * RationalSingletonProgram.inverseBound security order)

theorem singleton_bound (security order : ℕ) (horder : 1 ≤ order) (bodyRole : UniformBodyProfiles.BodyRole)
    (queue : ℤ) (root : Root security) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.singletonAt security order horder bodyRole queue root arity).val colors centers| ≤ singletonBound security order := by
  have h := product_bound order (data security order (RootReferenceColumns.singletonFirstAt security order horder bodyRole queue root))
    (data security order (RootMeanPrimary.positiveInverse security order horder bodyRole queue))
    (RationalSingletonProgram.firstBound security) (RationalSingletonProgram.inverseBound security order)
    (RationalSingletonProgram.firstBound_nonneg security) (RationalOrdinaryFamilyProgram.inverse_constants_nonneg security order).1
    (RationalSingletonProgram.actual_first_bound security order horder bodyRole queue root)
    (RationalSingletonProgram.actual_inverse_bound security order horder bodyRole queue) arity colors centers
  rw [data_product] at h
  exact h

def pointBound (security order : ℕ) : ℝ :=
  1 + |primaryBound security order| + |ordinaryBound security order| + |legBound security order| + |singletonBound security order|

theorem pointBound_one_le (security order : ℕ) : 1 ≤ pointBound security order := by
  unfold pointBound
  linarith [abs_nonneg (primaryBound security order), abs_nonneg (ordinaryBound security order),
    abs_nonneg (legBound security order), abs_nonneg (singletonBound security order)]

theorem local_bound {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : TaggedSelection.Selection security r s) (tagged : Finset (ActualBlockFock.BlockIndex security))
    (group : PairedRootPlacement.ActiveGroup selection tagged) (source : ActualRootGroupedChannel.Input selection tagged group)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.reducedColumn order horder queue selection tagged group source arity).val colors centers| ≤ pointBound security order := by
  have hp : primaryBound security order ≤ pointBound security order := by
    unfold pointBound
    linarith [le_abs_self (primaryBound security order), abs_nonneg (ordinaryBound security order),
      abs_nonneg (legBound security order), abs_nonneg (singletonBound security order)]
  have ho : ordinaryBound security order ≤ pointBound security order := by
    unfold pointBound
    linarith [le_abs_self (ordinaryBound security order), abs_nonneg (primaryBound security order),
      abs_nonneg (legBound security order), abs_nonneg (singletonBound security order)]
  have hl : legBound security order ≤ pointBound security order := by
    unfold pointBound
    linarith [le_abs_self (legBound security order), abs_nonneg (ordinaryBound security order),
      abs_nonneg (primaryBound security order), abs_nonneg (singletonBound security order)]
  have hs : singletonBound security order ≤ pointBound security order := by
    unfold pointBound
    linarith [le_abs_self (singletonBound security order), abs_nonneg (ordinaryBound security order),
      abs_nonneg (legBound security order), abs_nonneg (primaryBound security order)]
  rcases group with (primary | ordinary) | kept
  · exact (primary_bound security order _ source.2 arity colors centers).trans hp
  · exact (ordinary_bound security order horder source.2 (source.1 (0 : Fin 1)) arity colors centers).trans ho
  · rcases hk : kept.val.val with leg | (center | point)
    · simpa only [RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, hk] using
        (leg_bound security order horder (source.1 (0 : Fin 1)) arity colors centers).trans hl
    · simpa only [RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, hk] using
        (singleton_bound security order horder .free queue (source.1 (0 : Fin 1)) arity colors centers).trans hs
    · simpa only [RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, hk] using
        (singleton_bound security order horder .queue queue (source.1 (0 : Fin 1)) arity colors centers).trans hs

end
end CurrentAFT.RationalRootGroupProgram

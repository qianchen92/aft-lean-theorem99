import CurrentAFT.RationalOrdinaryNormalized
import CurrentAFT.RootWeightedSynthesis

/-! # All five actual local group columns in one rational dispatch program -/
namespace CurrentAFT.RationalRootGroupProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

inductive LocalRole where
  | primary | ordinary | leg | center | queue
  deriving DecidableEq

def localTable (security bits order : ℕ) (queue : ℤ) (role : LocalRole) (source : Fin 3 → ℕ) : Table ℚ ℕ ℕ order :=
  match role with
  | .primary => RationalPositiveFamilyProgram.primaryChannel security bits order (source 0) (source 1) (source 2)
  | .ordinary => RationalOrdinaryFamilyProgram.current security bits order (source 1) (source 0)
  | .leg => RationalUnselectedLegProgram.current security bits order (source 0)
  | .center => RationalSingletonProgram.current security bits order .free queue (source 0)
  | .queue => RationalSingletonProgram.current security bits order .queue queue (source 0)

noncomputable section
open scoped Classical
local instance groupProgramFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference PublicParameterProgram.modulus

def role {security r s : ℕ} (selection : TaggedSelection.Selection security r s)
    (tagged : Finset (ActualBlockFock.BlockIndex security)) : PairedRootPlacement.ActiveGroup selection tagged → LocalRole
  | .inl (.inl _) => .primary
  | .inl (.inr _) => .ordinary
  | .inr index => match index.val.val with
    | .inl _ => .leg
    | .inr (.inl _) => .center
    | .inr (.inr _) => .queue

def sourceNatural {security r s : ℕ} (selection : TaggedSelection.Selection security r s)
    (tagged : Finset (ActualBlockFock.BlockIndex security)) :
    (group : PairedRootPlacement.ActiveGroup selection tagged) → ActualRootGroupedChannel.Input selection tagged group → (Fin 3 → ℕ)
  | .inl (.inl _), source => ![(source.1 (0 : Fin 2)).val, (source.1 (1 : Fin 2)).val, source.2.val]
  | .inl (.inr _), source => ![(source.1 (0 : Fin 1)).val, source.2.val.val, 0]
  | .inr _, source => ![(source.1 (0 : Fin 1)).val, 0, 0]

def table {security r s : ℕ} (bits order : ℕ) (queue : ℤ) (selection : TaggedSelection.Selection security r s)
    (tagged : Finset (ActualBlockFock.BlockIndex security)) (group : PairedRootPlacement.ActiveGroup selection tagged)
    (source : ActualRootGroupedChannel.Input selection tagged group) : Table ℚ ℕ ℕ order :=
  localTable security bits order queue (role selection tagged group) (sourceNatural selection tagged group source)

def errorConstant (security order : ℕ) : ℝ :=
  |RationalNormalizedPrimaryProgram.primaryErrorConstant security order| +
    |RationalOrdinaryFamilyProgram.errorConstant security order| +
    |RationalUnselectedLegProgram.errorConstant security order| + |RationalSingletonProgram.errorConstant security order|

theorem errorConstant_nonneg (security order : ℕ) : 0 ≤ errorConstant security order := by unfold errorConstant; positivity

theorem local_error {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : TaggedSelection.Selection security r s) (tagged : Finset (ActualBlockFock.BlockIndex security))
    (group : PairedRootPlacement.ActiveGroup selection tagged) (source : ActualRootGroupedChannel.Input selection tagged group)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (table bits order queue selection tagged group source) arity colors centers -
      (RootReferenceColumns.reducedColumn order horder queue selection tagged group source arity).val colors centers| ≤
      errorConstant security order * (1 / (2 : ℝ)^bits) := by
  have he : 0 ≤ 1 / (2 : ℝ)^bits := by positivity
  have hp : RationalNormalizedPrimaryProgram.primaryErrorConstant security order ≤ errorConstant security order := by
    unfold errorConstant
    linarith [le_abs_self (RationalNormalizedPrimaryProgram.primaryErrorConstant security order),
      abs_nonneg (RationalOrdinaryFamilyProgram.errorConstant security order),
      abs_nonneg (RationalUnselectedLegProgram.errorConstant security order), abs_nonneg (RationalSingletonProgram.errorConstant security order)]
  have ho : RationalOrdinaryFamilyProgram.errorConstant security order ≤ errorConstant security order := by
    unfold errorConstant
    linarith [le_abs_self (RationalOrdinaryFamilyProgram.errorConstant security order),
      abs_nonneg (RationalNormalizedPrimaryProgram.primaryErrorConstant security order),
      abs_nonneg (RationalUnselectedLegProgram.errorConstant security order), abs_nonneg (RationalSingletonProgram.errorConstant security order)]
  have hl : RationalUnselectedLegProgram.errorConstant security order ≤ errorConstant security order := by
    unfold errorConstant
    linarith [le_abs_self (RationalUnselectedLegProgram.errorConstant security order),
      abs_nonneg (RationalNormalizedPrimaryProgram.primaryErrorConstant security order),
      abs_nonneg (RationalOrdinaryFamilyProgram.errorConstant security order), abs_nonneg (RationalSingletonProgram.errorConstant security order)]
  have hs : RationalSingletonProgram.errorConstant security order ≤ errorConstant security order := by
    unfold errorConstant
    linarith [le_abs_self (RationalSingletonProgram.errorConstant security order),
      abs_nonneg (RationalNormalizedPrimaryProgram.primaryErrorConstant security order),
      abs_nonneg (RationalUnselectedLegProgram.errorConstant security order), abs_nonneg (RationalOrdinaryFamilyProgram.errorConstant security order)]
  rcases group with (primary | ordinary) | kept
  · have h := RationalNormalizedPrimaryProgram.primaryChannel_error security bits order
      (RootPrimaryGroupedChannel.pairEquiv security source.1) source.2 hfirst hprecision hbudget arity colors centers
    exact h.trans (mul_le_mul_of_nonneg_right hp he)
  · exact (RationalOrdinaryFamilyProgram.current_error security bits order horder source.2 (source.1 (0 : Fin 1))
      hfirst hprecision hbudget arity colors centers).trans (mul_le_mul_of_nonneg_right ho he)
  · rcases hk : kept.val.val with leg | (center | point)
    · simpa only [table, role, hk, sourceNatural, localTable, Matrix.cons_val_zero,
        RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, interpret, realTable, pullback] using
        (RationalUnselectedLegProgram.current_error security bits order horder (source.1 (0 : Fin 1))
          hfirst hprecision hbudget arity colors centers).trans (mul_le_mul_of_nonneg_right hl he)
    · simpa only [table, role, hk, sourceNatural, localTable, Matrix.cons_val_zero,
        RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, interpret, realTable, pullback] using
        (RationalSingletonProgram.current_error security bits order horder .free queue (source.1 (0 : Fin 1))
          hfirst hprecision hbudget arity colors centers).trans (mul_le_mul_of_nonneg_right hs he)
    · simpa only [table, role, hk, sourceNatural, localTable, Matrix.cons_val_zero,
        RootReferenceColumns.reducedColumn, RootReferenceColumns.unselectedAt, interpret, realTable, pullback] using
        (RationalSingletonProgram.current_error security bits order horder .queue queue (source.1 (0 : Fin 1))
          hfirst hprecision hbudget arity colors centers).trans (mul_le_mul_of_nonneg_right hs he)

end
end CurrentAFT.RationalRootGroupProgram

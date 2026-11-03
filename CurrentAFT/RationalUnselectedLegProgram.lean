import CurrentAFT.RationalLegMassProgram
import CurrentAFT.LegCoefficientPointBounds
import CurrentAFT.RationalSingletonProgram
import CurrentAFT.RationalActualFamilyApproximation

/-! # The complete actual unselected leg with its pure-primary denominator -/
namespace CurrentAFT.RationalUnselectedLegProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def higher (security bits order : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  RationalLegFamilyTable.higher security bits order (RationalLegMassProgram.difference security bits root)

def positive (security bits order : ℕ) : Table ℚ ℕ ℕ order :=
  RationalLegFamilyTable.positive security bits order (RationalLegMassProgram.mean security bits)

def inverse (security bits order : ℕ) : Table ℚ ℕ ℕ order := reciprocal order (positive security bits order)

def numerator (security bits order : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  RationalSingletonProgram.first security bits order .attachment 0 root + higher security bits order root

def current (security bits order : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  product order (numerator security bits order root) (inverse security bits order)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw

def higherError (security : ℕ) : ℝ :=
  RationalLegFamilyTable.higherError security 2 (RationalLegMassProgram.differenceErrorConstant security)

def positiveError (security : ℕ) : ℝ :=
  RationalLegFamilyTable.positiveError security (RationalLegMassProgram.meanErrorConstant security)

theorem mass_difference_bound (security : ℕ) (root : ℤ) (word : Fin 3 → Palette security) :
    |(ActualBlockFock.primaryLawAt security root).weight word - RootTaggedLegHigher.rawMassLinear security 1 word| ≤ 2 := by
  have hmean : RootTaggedLegHigher.rawMassLinear security 1 word = (RootLegReciprocal.meanPositiveLaw security).weight word :=
    (congrFun (RootLegReciprocal.meanPositiveLaw_weight security) word).symm
  rw [hmean]
  have hfirst : |(ActualBlockFock.primaryLawAt security root).weight word| ≤ 1 := by
    rw [abs_of_nonneg ((ActualBlockFock.primaryLawAt security root).nonneg word)]
    exact (ActualBlockFock.primaryLawAt security root).atom_le_one word
  have hsecond : |(RootLegReciprocal.meanPositiveLaw security).weight word| ≤ 1 := by
    rw [abs_of_nonneg ((RootLegReciprocal.meanPositiveLaw security).nonneg word)]
    exact (RootLegReciprocal.meanPositiveLaw security).atom_le_one word
  exact (abs_sub _ _).trans ((add_le_add hfirst hsecond).trans_eq (by norm_num))

theorem higher_error (security bits order : ℕ) (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(higher security bits order root.val arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.legHigherAt security order root arity).val colors centers| ≤
      higherError security * (1 / (2 : ℝ)^bits) := by
  exact RationalLegFamilyTable.higher_error security bits order (RationalLegMassProgram.difference security bits root.val)
    ((ActualBlockFock.primaryLawAt security root.val).weight - RootTaggedLegHigher.rawMassLinear security 1)
    2 (RationalLegMassProgram.differenceErrorConstant security) (by norm_num)
    (RationalLegMassProgram.errorConstants_nonneg security).2 (mass_difference_bound security root.val)
    (RationalLegMassProgram.difference_error security bits root.val hprecision hbudget)
    hfirst hprecision hbudget arity colors centers

theorem positive_error (security bits order : ℕ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(positive security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootLegReciprocal.positive security order arity).val colors centers| ≤
      positiveError security * (1 / (2 : ℝ)^bits) := by
  apply RationalLegFamilyTable.positive_error security bits order (RationalLegMassProgram.mean security bits)
    (RootLegReciprocal.meanPositiveLaw security) (RationalLegMassProgram.meanErrorConstant security)
    (RationalLegMassProgram.errorConstants_nonneg security).1 _ hfirst hprecision hbudget arity colors centers
  intro word
  rw [RootLegReciprocal.meanPositiveLaw_weight]
  exact RationalLegMassProgram.mean_error security bits hprecision hbudget word

theorem error_constants_nonneg (security : ℕ) : 0 ≤ higherError security ∧ 0 ≤ positiveError security := by
  constructor
  · unfold higherError RationalLegFamilyTable.higherError
    exact Finset.sum_nonneg (fun selected _ => RationalLegFamilyTable.normalizedError_nonneg security selected.card 2 _
      (by norm_num) (RationalLegMassProgram.errorConstants_nonneg security).2)
  · unfold positiveError RationalLegFamilyTable.positiveError
    exact Finset.sum_nonneg (fun selected _ => RationalLegFamilyTable.normalizedError_nonneg security selected.card 1 _
      (by norm_num) (RationalLegMassProgram.errorConstants_nonneg security).1)

end
end CurrentAFT.RationalUnselectedLegProgram

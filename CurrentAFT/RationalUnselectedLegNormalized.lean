import CurrentAFT.RationalUnselectedLegProgram

/-! # Accuracy of the original complete pure-primary unselected leg column -/
namespace CurrentAFT.RationalUnselectedLegProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance normalizedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def positiveBound (security : ℕ) : ℝ := 1 + 8 * LegCoefficientPointBounds.selectedBound security 1

theorem positiveBound_nonneg (security : ℕ) : 0 ≤ positiveBound security := by
  unfold positiveBound
  positivity [LegCoefficientPointBounds.selectedBound_nonneg security 1 (by norm_num)]

theorem actual_positive_bound (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegReciprocal.positive security order arity).val colors centers| ≤ positiveBound security :=
  LegCoefficientPointBounds.positive_bound security order (RootLegReciprocal.meanPositiveLaw security) arity colors centers

theorem inverse_interpret (security bits order : ℕ) :
    interpret security order (inverse security bits order) = reciprocal order (interpret security order (positive security bits order)) := by
  unfold interpret inverse
  rw [reciprocal_cast, pullback_reciprocal]

theorem inverse_actual (security order : ℕ) :
    reciprocal order (fun arity => (RootLegReciprocal.positive security order arity).val) =
      fun arity => (RootLegReciprocal.reciprocal security order arity).val := by
  rw [reciprocal_actual]
  rfl

def inverseBound (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ) * (growth order (1 + positiveBound security) 0)^order

def inverseError (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ)^2 * positiveError security *
    (growth order (1 + positiveBound security) (positiveError security))^(order + 1)

theorem inverse_constants_nonneg (security order : ℕ) : 0 ≤ inverseBound security order ∧ 0 ≤ inverseError security order := by
  have hA := positiveBound_nonneg security
  have hE := (error_constants_nonneg security).2
  have hg0 := growth_ge_one order (1 + positiveBound security) 0 (by positivity) (by norm_num)
  have hg := growth_ge_one order (1 + positiveBound security) (positiveError security) (by positivity) hE
  constructor
  · unfold inverseBound; positivity
  · unfold inverseError; positivity

theorem actual_inverse_bound (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootLegReciprocal.reciprocal security order arity).val colors centers| ≤ inverseBound security order := by
  have h := reciprocal_bound order (fun arity => (RootLegReciprocal.positive security order arity).val)
    (positiveBound security) (positiveBound_nonneg security) (actual_positive_bound security order) arity colors centers
  rw [inverse_actual] at h
  exact h

theorem inverse_error (security bits order : ℕ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (inverse security bits order) arity colors centers -
      (RootLegReciprocal.reciprocal security order arity).val colors centers| ≤
      inverseError security order * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let E := positiveError security
  let A := positiveBound security
  have he : 0 ≤ epsilon := by positivity
  have hE : 0 ≤ E := (error_constants_nonneg security).2
  have hA : 0 ≤ A := positiveBound_nonneg security
  have h := reciprocal_error order (fun arity => (RootLegReciprocal.positive security order arity).val)
    (interpret security order (positive security bits order)) A (E * epsilon) hA (by positivity)
    (actual_positive_bound security order) (positive_error security bits order hfirst hprecision hbudget) arity colors centers
  rw [← inverse_interpret, inverse_actual] at h
  have hsmall : E * epsilon ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (RationalCoefficientExtraction.epsilon_le_one bits) hE
  have hg : growth order (1 + A) (E * epsilon) ≤ growth order (1 + A) E := by unfold growth; gcongr
  have hg0 : 0 ≤ growth order (1 + A) (E * epsilon) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (growth_ge_one order (1 + A) (E * epsilon) (by positivity) (by positivity))
  calc
    _ ≤ _ := h
    _ ≤ ((order + 1 : ℕ) : ℝ)^2 * (E * epsilon) * (growth order (1 + A) E)^(order + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg _) (by positivity)
    _ = _ := by unfold inverseError; dsimp only [E, A, epsilon]; ring

def numeratorActual (security order : ℕ) (horder : 1 ≤ order) (root : CycleRootExpansion.Root security) :
    BackgroundFamilies.ActualFamily security order :=
  RootReferenceColumns.singletonFirstAt security order horder .attachment 0 root + RootReferenceColumns.legHigherAt security order root

def numeratorBound (security : ℕ) : ℝ :=
  RationalSingletonProgram.firstBound security + 8 * LegCoefficientPointBounds.selectedBound security 2

def numeratorError (security : ℕ) : ℝ := RationalRootProfileProgram.firstErrorConstant security + higherError security

theorem numerator_constants_nonneg (security : ℕ) : 0 ≤ numeratorBound security ∧ 0 ≤ numeratorError security := by
  exact ⟨add_nonneg (RationalSingletonProgram.firstBound_nonneg security)
    (mul_nonneg (by norm_num) (LegCoefficientPointBounds.selectedBound_nonneg security 2 (by norm_num))),
    add_nonneg (RationalRootProfileProgram.densityError_nonneg security).1 (error_constants_nonneg security).1⟩

theorem actual_numerator_bound (security order : ℕ) (horder : 1 ≤ order) (root : CycleRootExpansion.Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(numeratorActual security order horder root arity).val colors centers| ≤ numeratorBound security := by
  exact (abs_add_le _ _).trans (add_le_add
    (RationalSingletonProgram.actual_first_bound security order horder .attachment 0 root arity colors centers)
    (LegCoefficientPointBounds.higher_bound security order _ 2 (by norm_num) (mass_difference_bound security root.val) arity colors centers))

theorem numerator_error (security bits order : ℕ) (horder : 1 ≤ order) (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (numerator security bits order root.val) arity colors centers -
      (numeratorActual security order horder root arity).val colors centers| ≤
      numeratorError security * (1 / (2 : ℝ)^bits) := by
  have hf := RationalSingletonProgram.first_error security bits order horder .attachment 0 root hfirst hprecision hbudget arity colors centers
  have hh := higher_error security bits order root hfirst hprecision hbudget arity colors centers
  change |((RationalSingletonProgram.first security bits order .attachment 0 root.val arity _ _ +
    higher security bits order root.val arity _ _ : ℚ) : ℝ) -
    ((RootReferenceColumns.singletonFirstAt security order horder .attachment 0 root arity).val colors centers +
      (RootReferenceColumns.legHigherAt security order root arity).val colors centers)| ≤ _
  rw [Rat.cast_add]
  have hsplit := abs_add_le
    ((RationalSingletonProgram.first security bits order .attachment 0 root.val arity (fun index => (colors index).val)
      (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.singletonFirstAt security order horder .attachment 0 root arity).val colors centers)
    ((higher security bits order root.val arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.legHigherAt security order root arity).val colors centers)
  have hrhs : RationalRootProfileProgram.firstErrorConstant security * (1 / (2 : ℝ)^bits) +
      higherError security * (1 / (2 : ℝ)^bits) = numeratorError security * (1 / (2 : ℝ)^bits) := by
    unfold numeratorError
    ring
  convert hsplit.trans ((add_le_add hf hh).trans_eq hrhs) using 1
  congr 1
  dsimp only [Function.comp_def]
  ring

def errorConstant (security order : ℕ) : ℝ :=
  productError order (numeratorBound security) (inverseBound security order) (numeratorError security) (inverseError security order)

theorem current_error (security bits order : ℕ) (horder : 1 ≤ order) (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order root.val arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.legAt security order horder root arity).val colors centers| ≤
      errorConstant security order * (1 / (2 : ℝ)^bits) := by
  exact RationalActualFamilyApproximation.product_error security bits order
    (numeratorActual security order horder root) (RootLegReciprocal.reciprocal security order)
    (numerator security bits order root.val) (inverse security bits order)
    (numeratorBound security) (inverseBound security order) (numeratorError security) (inverseError security order)
    (numerator_constants_nonneg security).1 (inverse_constants_nonneg security order).1
    (numerator_constants_nonneg security).2 (inverse_constants_nonneg security order).2
    (actual_numerator_bound security order horder root) (actual_inverse_bound security order)
    (numerator_error security bits order horder root hfirst hprecision hbudget)
    (inverse_error security bits order hfirst hprecision hbudget) arity colors centers

end
end CurrentAFT.RationalUnselectedLegProgram

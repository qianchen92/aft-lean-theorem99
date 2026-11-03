import CurrentAFT.ActualCoordinateBounds

/-! # Polynomial point bounds for the actual independent positive family -/
namespace CurrentAFT.PositiveFamilyPointBound
open AFT ProposalPrimary ActualControls LocalCoefficientFamily NormalizedLocalPolynomial
  LocalRaisingBounds GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def bound (security order : ℕ) : ℝ :=
  (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^order * (1 + positiveConstant)

theorem norm_bound (security order : ℕ) :
    coefficientNorm security order (positiveFamily security order (independentPositiveLaw security)) ≤
      1 + positiveConstant := by
  have hadd := familyNorm_add_le (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (RaisingPatternBudget.primaryFactor_pos security).le (RaisingPatternBudget.bodyFactor_pos security).le
    (positiveFamily security order (independentPositiveLaw security) - 1) 1
  rw [sub_add_cancel, familyNorm_one] at hadd
  have hbase : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hden : (1 : ℝ) ≤ (Parameters.base security : ℝ)^39 := one_le_pow₀ hbase
  have hd := (independentPositive_defect security order).trans
    (div_le_self positiveConstant_nonneg hden)
  change coefficientNorm security order _ ≤ coefficientNorm security order _ + 1 at hadd
  linarith

theorem point_bound (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → ActualControls.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |((positiveFamily security order (independentPositiveLaw security)) arity).val colors centers| ≤ bound security order :=
  (ActualCoordinateBounds.family_point_bound security order _ arity colors centers).trans
    (mul_le_mul_of_nonneg_left (norm_bound security order) (by positivity))

theorem bound_nonneg (security order : ℕ) : 0 ≤ bound security order := by
  unfold bound
  positivity [positiveConstant_nonneg]

theorem bound_polynomial (security order : ℕ) :
    bound security order ≤ ((2 * 131072 * 131074 : ℝ)^order * (1 + positiveConstant)) *
      (Parameters.base security : ℝ)^(224 * order) := by
  exact (mul_le_mul_of_nonneg_right (ActualCoordinateBounds.coordinate_factor_polynomial security order)
    (by positivity [positiveConstant_nonneg])).trans_eq (by ring)

end
end CurrentAFT.PositiveFamilyPointBound

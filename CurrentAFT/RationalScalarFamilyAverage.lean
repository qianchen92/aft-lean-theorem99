import CurrentAFT.RationalActualFamilyApproximation
import CurrentAFT.RationalBackgroundLinearProgram

/-! # Averaging complete coefficient tables under the one shared scalar -/
namespace CurrentAFT.RationalScalarFamilyAverage
open AFT GaussianSource RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus

def current (security bits order : ℕ)
    (table : ℤ → RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => ∑ scalar : Window (RationalBackgroundLinearProgram.cutoff security),
    RationalProposalProgram.gaussianWeight security (RationalBackgroundLinearProgram.cutoff security) bits scalar*
      table scalar.val arity colors centers

noncomputable section
open scoped Classical
local instance scalarAverageFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def actual (security order : ℕ) (families : MarkedPairSeed.Scalar security → ActualFamily security order) :
    ActualFamily security order := ∑ scalar, (scalarLaw security).weight scalar • families scalar

theorem current_cast (security bits order : ℕ)
    (table : ℤ → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    interpret security order (current security bits order table) arity colors centers =
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security-1) bits).expectation
        (fun scalar => interpret security order (table scalar.val) arity colors centers) := by
  change (current security bits order table arity (fun index => (colors index).val)
    (fun index => (centers index).val.val):ℝ) = _
  unfold current
  rw [Rat.cast_sum, RationalBackgroundLinearProgram.cutoff_value]
  simp only [Rat.cast_mul, RationalProposalProgram.gaussianWeight_eq,
    FiniteDist.expectation, windowApproxLaw, interpret, RationalFamilyProductProgram.pullback,
    RationalFamilyProductProgram.realTable]
  rfl

theorem actual_data (security order : ℕ)
    (families : MarkedPairSeed.Scalar security → ActualFamily security order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    data security order (actual security order families) arity colors centers =
      (scalarLaw security).expectation (fun scalar => data security order (families scalar) arity colors centers) := by
  simp only [actual, data, FiniteDist.expectation, Finset.sum_apply, Submodule.coe_sum,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]

theorem current_error (security bits order : ℕ)
    (families : MarkedPairSeed.Scalar security → ActualFamily security order)
    (table : ℤ → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (B e : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ scalar arity colors centers, |data security order (families scalar) arity colors centers| ≤ B)
    (herror : ∀ scalar arity colors centers,
      |interpret security order (table scalar.val) arity colors centers-
        data security order (families scalar) arity colors centers| ≤ e*(1/(2:ℝ)^bits))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (current security bits order table) arity colors centers-
      data security order (actual security order families) arity colors centers| ≤ (e+B)*(1/(2:ℝ)^bits) := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security-1) bits
  let computed := fun scalar : MarkedPairSeed.Scalar security => interpret security order (table scalar.val) arity colors centers
  let ideal := fun scalar : MarkedPairSeed.Scalar security => data security order (families scalar) arity colors centers
  have hpoint := CalibrationCoordinateError.expectation_abs_bound approximate
    (fun scalar => computed scalar-ideal scalar) (e*(1/(2:ℝ)^bits))
    (fun scalar => herror scalar arity colors centers)
  rw [FiniteDist.expectation_sub] at hpoint
  have hl1 := windowApproxLaw_l1 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security-1) bits (WindowGaussianSampler.squaredWidth_positive security)
    (WindowGaussianSampler.squaredWidth_real security).symm
  have hsource := (CyclePatternProgram.expectation_difference_le_l1 approximate (scalarLaw security) ideal B
    (fun scalar => hbound scalar arity colors centers)).trans (mul_le_mul_of_nonneg_left hl1 hB)
  rw [current_cast, actual_data]
  exact (abs_sub_le _ (approximate.expectation ideal) _).trans
    ((add_le_add hpoint hsource).trans_eq (by ring))

end
end CurrentAFT.RationalScalarFamilyAverage

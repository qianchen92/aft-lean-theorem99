import CurrentAFT.RationalBackgroundProgram
import CurrentAFT.BackgroundLinear
import CurrentAFT.ActualCoordinateBounds

/-! # The same-scalar average and the original balanced leg-linear data -/
namespace CurrentAFT.RationalBackgroundLinearProgram
open AFT GaussianSource RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles ProposalPrimary BackgroundFamilies
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw

def cutoff (security : ℕ) : ℕ := (security+2)^2-1

def meanTranslation (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => ∑ scalar : Window (cutoff security),
    RationalProposalProgram.gaussianWeight security (cutoff security) bits scalar*
      RationalBackgroundProgram.translation security bits order scalar.val arity colors centers

def freeMass (security : ℕ) : ℚ :=
  ((PublicParameterProgram.modulus security).count:ℚ)*(security+2)^96-(security+2)^128-(PublicParameterProgram.modulus security).count

def legLinear (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers =>
    -(freeMass security*RationalBackgroundProgram.free security bits order arity colors centers+
      ((PublicParameterProgram.modulus security).count:ℚ)*meanTranslation security bits order arity colors centers)/((security+2:ℚ)^128)

noncomputable section
open scoped Classical
local instance linearFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem cutoff_value (security : ℕ) : cutoff security = Parameters.sourceCutoff security-1 := by
  simp only [cutoff, Parameters.sourceCutoff, Parameters.base]

def translationBound (security order : ℕ) : ℝ := 56*(2*(Parameters.modulus security:ℝ)*Parameters.dimension security)^order

def meanErrorConstant (security order : ℕ) : ℝ := RationalBackgroundProgram.translationErrorConstant security+translationBound security order

def linearErrorConstant (security order : ℕ) : ℝ :=
  (ProposalPrimary.freeMass security*RationalBackgroundProgram.freeErrorConstant security+
    (Parameters.modulus security:ℝ)*meanErrorConstant security order)/(Parameters.legCount security:ℝ)

theorem translation_bound (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(translationCertificate security order horder shift arity).val colors centers| ≤ translationBound security order := by
  have hb : (1:ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by decide : 1≤2)
  have hn : LocalRaisingBounds.coefficientNorm security order (translationCertificate security order horder shift) ≤ 56 := by
    apply (translationCertificate_norm_decay security order horder shift).trans
    exact div_le_self (by norm_num) (one_le_pow₀ hb)
  exact (ActualCoordinateBounds.family_point_bound security order (translationCertificate security order horder shift) arity colors centers).trans
    ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by unfold translationBound; ring))

theorem meanTranslation_cast (security bits order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → FirstHistogram.Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    (meanTranslation security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ) =
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security-1) bits).expectation
        (fun scalar => (RationalBackgroundProgram.translation security bits order scalar.val arity
          (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)) := by
  unfold meanTranslation
  rw [Rat.cast_sum, cutoff_value]
  simp only [Rat.cast_mul, RationalProposalProgram.gaussianWeight_eq, FiniteDist.expectation, windowApproxLaw]

theorem meanTranslation_actual (security order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → FirstHistogram.Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    (scalarLaw security).expectation (fun scalar => (translationCertificate security order horder scalar.val arity).val colors centers) =
      (BackgroundLinear.meanTranslation security order horder arity).val colors centers := by
  simp only [BackgroundLinear.meanTranslation, FiniteDist.expectation, Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul]

theorem meanTranslation_error (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(meanTranslation security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (BackgroundLinear.meanTranslation security order horder arity).val colors centers| ≤ meanErrorConstant security order*(1/(2:ℝ)^bits) := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security-1) bits
  let computed := fun scalar : MarkedPairSeed.Scalar security =>
    (RationalBackgroundProgram.translation security bits order scalar.val arity
      (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)
  let ideal := fun scalar : MarkedPairSeed.Scalar security => (translationCertificate security order horder scalar.val arity).val colors centers
  have hl1 := windowApproxLaw_l1 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security-1) bits (WindowGaussianSampler.squaredWidth_positive security) (WindowGaussianSampler.squaredWidth_real security).symm
  have hpoint := CalibrationCoordinateError.expectation_abs_bound approximate (computed-ideal)
    (RationalBackgroundProgram.translationErrorConstant security*(1/(2:ℝ)^bits))
    (fun scalar => RationalBackgroundProgram.translation_error security bits order horder scalar.val hfirst hprecision hbudget arity colors centers)
  change |approximate.expectation (fun scalar => computed scalar-ideal scalar)| ≤ _ at hpoint
  rw [FiniteDist.expectation_sub] at hpoint
  have hsource := (CyclePatternProgram.expectation_difference_le_l1 approximate (scalarLaw security) ideal
    (translationBound security order) (fun scalar => translation_bound security order horder scalar.val arity colors centers)).trans
    (mul_le_mul_of_nonneg_left hl1 (by unfold translationBound; positivity))
  rw [meanTranslation_cast, ← meanTranslation_actual security order horder]
  exact (abs_sub_le _ (approximate.expectation ideal) _).trans ((add_le_add hpoint hsource).trans_eq (by unfold meanErrorConstant; ring))

theorem freeMass_cast (security : ℕ) : (freeMass security:ℝ) = ProposalPrimary.freeMass security := by
  simp only [freeMass, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat, PublicParameterProgram.modulus_value,
    ProposalPrimary.freeMass, Parameters.bodySize_eq, Parameters.legCount_eq, Parameters.base, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]

theorem legLinear_cast (security bits order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    (legLinear security bits order arity (fun index => (colors index).val)
      (fun index => (centers index).val.val):ℝ) =
      -(ProposalPrimary.freeMass security *
        (RationalBackgroundProgram.free security bits order arity (fun index => (colors index).val)
          (fun index => (centers index).val.val):ℝ) +
        (Parameters.modulus security:ℝ) *
        (meanTranslation security bits order arity (fun index => (colors index).val)
          (fun index => (centers index).val.val):ℝ)) / Parameters.legCount security := by
  simp only [legLinear, Rat.cast_div, Rat.cast_neg, Rat.cast_add, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, freeMass_cast,
    PublicParameterProgram.modulus_value, Parameters.legCount_eq, Parameters.base,
    Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]

theorem legLinear_data (security order : ℕ) (horder : 1 ≤ order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    -(ProposalPrimary.freeMass security * (freeCertificate security order horder arity).val colors centers +
      (Parameters.modulus security:ℝ) * (BackgroundLinear.meanTranslation security order horder arity).val colors centers) /
        Parameters.legCount security =
      (BackgroundLinear.legLinearCertificate security order horder arity).val colors centers := by
  simp only [BackgroundLinear.legLinearCertificate, Pi.add_apply, Pi.smul_apply,
    Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  ring

theorem legLinear_error (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(legLinear security bits order arity (fun index => (colors index).val)
        (fun index => (centers index).val.val):ℝ) -
      (BackgroundLinear.legLinearCertificate security order horder arity).val colors centers| ≤
        linearErrorConstant security order * (1/(2:ℝ)^bits) := by
  have hf := RationalBackgroundProgram.free_error security bits order horder hfirst hprecision hbudget arity colors centers
  have hm := meanTranslation_error security bits order horder hfirst hprecision hbudget arity colors centers
  have hfree := ProposalPrimary.freeMass_nonneg security
  have hq := (FirstResponse.modulus_pos security).le
  have hlegs := BackgroundLinear.legCount_pos security
  rw [legLinear_cast, ← legLinear_data security order horder arity colors centers]
  rw [show -(ProposalPrimary.freeMass security *
      (RationalBackgroundProgram.free security bits order arity (fun index => (colors index).val)
        (fun index => (centers index).val.val):ℝ) + (Parameters.modulus security:ℝ) *
      (meanTranslation security bits order arity (fun index => (colors index).val)
        (fun index => (centers index).val.val):ℝ)) / Parameters.legCount security -
      -(ProposalPrimary.freeMass security * (freeCertificate security order horder arity).val colors centers +
        (Parameters.modulus security:ℝ) * (BackgroundLinear.meanTranslation security order horder arity).val colors centers) /
        Parameters.legCount security =
      -(ProposalPrimary.freeMass security *
        ((RationalBackgroundProgram.free security bits order arity (fun index => (colors index).val)
          (fun index => (centers index).val.val):ℝ) - (freeCertificate security order horder arity).val colors centers) +
        (Parameters.modulus security:ℝ) *
        ((meanTranslation security bits order arity (fun index => (colors index).val)
          (fun index => (centers index).val.val):ℝ) -
          (BackgroundLinear.meanTranslation security order horder arity).val colors centers)) /
          Parameters.legCount security by ring]
  rw [abs_div, abs_neg, abs_of_pos hlegs]
  calc
    _ ≤ (ProposalPrimary.freeMass security * (RationalBackgroundProgram.freeErrorConstant security*(1/(2:ℝ)^bits)) +
        (Parameters.modulus security:ℝ) * (meanErrorConstant security order*(1/(2:ℝ)^bits))) /
          Parameters.legCount security := by
      apply div_le_div_of_nonneg_right _ hlegs.le
      exact (abs_add_le _ _).trans (by
        simpa only [abs_mul, abs_of_nonneg hfree, abs_of_nonneg hq] using
          add_le_add (mul_le_mul_of_nonneg_left hf hfree) (mul_le_mul_of_nonneg_left hm hq))
    _ = _ := by unfold linearErrorConstant; ring

end
end CurrentAFT.RationalBackgroundLinearProgram

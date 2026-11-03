import CurrentAFT.RationalMassCertificateTable
import CurrentAFT.PrimaryDeviationCertificate

/-! # The original primary-deviation certificate as a rational table -/
namespace CurrentAFT.RationalPrimaryDeviationProgram
open AFT RationalNumerics GradedControlAlgebra ActualControls DiffuseProfiles ProposalPrimary
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw

def profile (security bits output : ℕ) : ℚ :=
  RationalProposalProgram.primary security bits output -
    1/((PublicParameterProgram.modulus security).count:ℚ)

def current (security bits order : ℕ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order
    (RationalMassLiftProgram.current security bits (profile security bits)) (fun _ => 0)

noncomputable section
open scoped Classical
local instance deviationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def profileErrorConstant (security : ℕ) : ℝ :=
  64*(Parameters.base security:ℝ)*Parameters.dimension security

def errorConstant (security : ℕ) : ℝ :=
  2*RationalMassLiftProgram.errorConstant security+
    RationalTensorInverseProgram.actualBound security*profileErrorConstant security

theorem profile_bound (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(profile security bits output.val:ℝ)| ≤ 2 := by
  have hp0 := (RationalProposalProgram.approximatePrimaryLaw security bits).nonneg output
  have hp1 := (RationalProposalProgram.approximatePrimaryLaw security bits).atom_le_one output
  change 0 ≤ (RationalProposalProgram.primary security bits output.val:ℝ) at hp0
  change (RationalProposalProgram.primary security bits output.val:ℝ) ≤ 1 at hp1
  have hq : (1:ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Nat.succ_le_of_lt (Parameters.modulus_spec security).2.pos)
  have hu : 1/(Parameters.modulus security:ℝ) ≤ 1 := by
    exact (div_le_one (FirstResponse.modulus_pos security)).mpr hq
  simp only [profile, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    PublicParameterProgram.modulus_value]
  rw [abs_sub_le_iff]
  constructor <;> linarith [div_nonneg (show (0:ℝ)≤1 by norm_num) (FirstResponse.modulus_pos security).le]

theorem profile_error (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(profile security bits output.val:ℝ)-PrimaryDeviationCertificate.deviation security output| ≤
      profileErrorConstant security*(1/(2:ℝ)^bits) := by
  simpa only [profile, Rat.cast_sub, Rat.cast_div, Rat.cast_inv, Rat.cast_one, Rat.cast_natCast,
    PublicParameterProgram.modulus_value, PrimaryDeviationCertificate.deviation, Pi.sub_apply,
    FringeCertificate.uniformProfile, one_div, sub_sub_sub_cancel_right, profileErrorConstant, primaryLaw] using
    RationalProposalProgram.primary_error security bits output hprecision hbudget

theorem data (security order : ℕ) (horder : 1 ≤ order) :
    RationalBackgroundTable.firstTable order
      (RationalMassLiftProgram.actual security (PrimaryDeviationCertificate.deviation security))
      (fun _ : SafePalette security => (0:ℝ)) =
      fun arity => (PrimaryDeviationCertificate.certificate security order horder arity).val := by
  exact RationalMassCertificateTable.data security order horder (PrimaryDeviationCertificate.deviation security)
    (PrimaryMassFamilies.oneWordProfile_centered _ (PrimaryDeviationCertificate.deviation_mass security))
    (PrimaryMassFamilies.oneWordProfile_symmetric _)

theorem errorConstant_nonneg (security : ℕ) : 0 ≤ errorConstant security := by
  simp only [errorConstant, profileErrorConstant, RationalMassLiftProgram.errorConstant,
    RationalTensorInverseProgram.actualBound, RationalDensityInverseProgram.inverseBound,
    RationalFirstResponseProgram.inverseErrorConstant]
  positivity

theorem current_error (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (PrimaryDeviationCertificate.certificate security order horder arity).val colors centers| ≤
      errorConstant security*(1/(2:ℝ)^bits) := by
  have hl (primary : FirstHistogram.Palette security) :
      |(RationalMassLiftProgram.current security bits (profile security bits) primary.val:ℝ)-
        RationalMassLiftProgram.actual security (PrimaryDeviationCertificate.deviation security) primary| ≤
        errorConstant security*(1/(2:ℝ)^bits) := by
    exact (RationalMassLiftProgram.current_profile_error security bits (profile security bits)
      (PrimaryDeviationCertificate.deviation security) 2 (profileErrorConstant security*(1/(2:ℝ)^bits))
      (by norm_num) (by unfold profileErrorConstant; positivity)
      (profile_bound security bits) (fun output => profile_error security bits output hprecision hbudget)
      hfirst hprecision hbudget primary).trans_eq (by unfold errorConstant; ring)
  have hx := RationalBackgroundTable.firstTable_error order
    (RationalMassLiftProgram.current security bits (profile security bits)) (fun _ => 0)
    (RationalMassLiftProgram.actual security (PrimaryDeviationCertificate.deviation security)) (fun _ : SafePalette security => 0)
    Fin.val (fun color => color.val.val) (errorConstant security*(1/(2:ℝ)^bits)) 0
    (mul_nonneg (errorConstant_nonneg security) (by positivity)) (by norm_num) hl (fun _ => by norm_num) arity colors centers
  rw [data security order horder] at hx
  simpa only [add_zero] using hx

end
end CurrentAFT.RationalPrimaryDeviationProgram

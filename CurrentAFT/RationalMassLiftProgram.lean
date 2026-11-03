import CurrentAFT.RationalDensityInverseProgram
import CurrentAFT.RationalTensorInverseProgram
import CurrentAFT.RootTaggedLocal
import CurrentAFT.PrimaryMassFamilies

/-! # Actual first mass lift with a rational rank-one inverse

The mass profile is passed directly to the first inverse. Activation and
the primary output atom are the only additional denominators, with proved
polynomial lower bounds. Input profile approximation is handled separately.
-/
namespace CurrentAFT.RationalMassLiftProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current (security bits : ℕ) (profile : ℕ → ℚ) (output : ℕ) : ℚ :=
  RationalFirstResponseProgram.inverse security bits profile output /
    (LocalPairProgram.activationApprox security bits * primary security bits output)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw

def actual (security : ℕ) : (Palette security → ℝ) →ₗ[ℝ] (Palette security → ℝ) :=
  (PrimaryTensorInverse.densityInverse security).comp (RootTaggedLocal.profileDensity security)

theorem actual_formula (security : ℕ) (profile : Palette security → ℝ) (output : Palette security) :
    actual security profile output = (FirstResponse.responseEquiv security).symm profile output /
      (activation security * (primaryLaw security).weight output) := by
  change PrimaryTensorInverse.densityInverse security (RootTaggedLocal.profileDensity security profile) output = _
  rw [PrimaryTensorInverse.densityInverse_apply]
  have hprofile : (fun color => (primaryLaw security).weight color * RootTaggedLocal.profileDensity security profile color) = profile := by
    funext color
    rw [RootTaggedLocal.profileDensity_apply]
    field_simp [(primaryReference_positive security color).ne']
  rw [hprofile]
  ring

theorem actual_denominator_lower (security : ℕ) (output : Palette security) :
    1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security) ≤
      activation security * (primaryLaw security).weight output := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hp : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security output
  calc
    _ = (1 / (4 * (Parameters.base security : ℝ))) * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
    _ ≤ _ := mul_le_mul (FirstResponse.activation_lower_simple security) hp (by positivity) (activation_pos security).le

theorem approximate_denominator_lower (security bits : ℕ) (output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits) :
    1 / (32 * (Parameters.base security : ℝ) * Parameters.modulus security) ≤
      (LocalPairProgram.activationApprox security bits : ℝ) * (primary security bits output.val : ℝ) := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have ha := RationalDensityInverseProgram.activationApprox_lower security bits hfirst
  have hp := RationalProposalProgram.primary_lower security bits output
  calc
    _ = (1 / (8 * (Parameters.base security : ℝ))) * (1 / (4 * (Parameters.modulus security : ℝ))) := by ring
    _ ≤ _ := mul_le_mul ha hp (by positivity) (LocalPairProgram.activationApprox_bounds security bits).1

theorem denominator_error (security bits : ℕ) (output : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(LocalPairProgram.activationApprox security bits : ℝ) * (primary security bits output.val : ℝ) -
      activation security * (primaryLaw security).weight output| ≤
      (1 / 2 + 64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits) := by
  have hp : |(primary security bits output.val : ℝ) - (primaryLaw security).weight output| ≤
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits) := by
    simpa only [primaryLaw] using primary_error security bits output hprecision hbudget
  have ha := LocalPairProgram.activationApprox_error security bits
  have hpa : 0 ≤ (primary security bits output.val : ℝ) := (approximatePrimaryLaw security bits).nonneg output
  have hpa1 := (approximatePrimaryLaw security bits).atom_le_one output
  have har : |activation security| ≤ 1 := by
    rw [abs_of_pos (activation_pos security)]
    exact (activation_le_half security).trans (by norm_num)
  calc
    _ = |((LocalPairProgram.activationApprox security bits : ℝ) - activation security) *
          (primary security bits output.val : ℝ) + activation security *
          ((primary security bits output.val : ℝ) - (primaryLaw security).weight output)| := by congr 1; ring
    _ ≤ |(LocalPairProgram.activationApprox security bits : ℝ) - activation security| * (primary security bits output.val : ℝ) +
      |activation security| * |(primary security bits output.val : ℝ) - (primaryLaw security).weight output| := by
        simpa only [abs_mul, abs_of_nonneg hpa] using abs_add_le
          (((LocalPairProgram.activationApprox security bits : ℝ) - activation security) * (primary security bits output.val : ℝ))
          (activation security * ((primary security bits output.val : ℝ) - (primaryLaw security).weight output))
    _ ≤ ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) * 1 +
      1 * ((64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits)) :=
        add_le_add (mul_le_mul ha hpa1 hpa (by positivity)) (mul_le_mul har hp (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem actual_bound (security : ℕ) (profile : Palette security → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hprofile : ∀ color, |profile color| ≤ bound) (output : Palette security) :
    |actual security profile output| ≤ RationalTensorInverseProgram.actualBound security * bound := by
  have hq := FirstResponse.modulus_pos security
  have hbase := FirstResponse.base_pos security
  have hden := actual_denominator_lower security output
  have hpos : 0 < activation security * (primaryLaw security).weight output :=
    mul_pos (activation_pos security) (primaryReference_positive security output)
  rw [actual_formula, abs_div, abs_of_pos hpos]
  calc
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
      (activation security * (primaryLaw security).weight output) :=
      div_le_div_of_nonneg_right
        (RationalDensityInverseProgram.actual_inverse_bound security profile bound hb hprofile output) hpos.le
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
      (1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security)) :=
      div_le_div_of_nonneg_left (by unfold RationalDensityInverseProgram.inverseBound; positivity) (by positivity) hden
    _ = _ := by unfold RationalTensorInverseProgram.actualBound; ring_nf; simp only [inv_inv]

theorem actual_profile_difference (security : ℕ) (first second : Palette security → ℝ)
    (error : ℝ) (he : 0 ≤ error) (hdiff : ∀ color, |first color - second color| ≤ error) (output : Palette security) :
    |actual security first output - actual security second output| ≤ RationalTensorInverseProgram.actualBound security * error := by
  have h := actual_bound security (first - second) error he hdiff output
  simpa only [map_sub, Pi.sub_apply] using h

theorem massLift_one (security : ℕ) (profile : Palette security → ℝ) (word : Fin 1 → Palette security) :
    PrimaryTensorInverse.massLift security 1 (PrimaryMassFamilies.oneWordProfile profile) word =
      actual security profile (word 0) := by
  unfold PrimaryTensorInverse.massLift
  change PrimaryTensorInverse.densityInverse security
    (fun color => PrimaryTensorInverse.massDensity security 1 (PrimaryMassFamilies.oneWordProfile profile)
      (Fin.cons color Fin.elim0)) (word 0) =
    PrimaryTensorInverse.densityInverse security (RootTaggedLocal.profileDensity security profile) (word 0)
  apply congrArg (fun input : Palette security → ℝ => PrimaryTensorInverse.densityInverse security input (word 0))
  funext color
  simp only [PrimaryTensorInverse.massDensity, PrimaryTensorInverse.referenceWeight, PrimaryMassFamilies.oneWordProfile,
    Fin.prod_univ_one, Fin.cons_zero, RootTaggedLocal.profileDensity_apply]

def errorConstant (security : ℕ) : ℝ :=
  (32 * (Parameters.base security : ℝ) * Parameters.modulus security) * RationalFirstResponseProgram.inverseErrorConstant security +
    RationalDensityInverseProgram.inverseBound security * (32 * (Parameters.base security : ℝ) * Parameters.modulus security)^2 *
      (1 / 2 + 64 * (Parameters.base security : ℝ) * Parameters.dimension security)

theorem errorConstant_nonneg (security : ℕ) : 0 ≤ errorConstant security := by
  unfold errorConstant RationalDensityInverseProgram.inverseBound RationalFirstResponseProgram.inverseErrorConstant
  positivity

theorem current_error (security bits : ℕ) (profile : ℕ → ℚ) (bound : ℝ) (hb : 0 ≤ bound)
    (hprofile : ∀ color : Palette security, |(profile color.val : ℝ)| ≤ bound)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(current security bits profile output.val : ℝ) - actual security (fun color => (profile color.val : ℝ)) output| ≤
      errorConstant security * bound * (1 / (2 : ℝ)^bits) := by
  let lower : ℝ := 1 / (32 * (Parameters.base security : ℝ) * Parameters.modulus security)
  have hb0 := FirstResponse.base_pos security
  have hq0 := FirstResponse.modulus_pos security
  have hi : 0 ≤ RationalFirstResponseProgram.inverseErrorConstant security := by
    unfold RationalFirstResponseProgram.inverseErrorConstant
    positivity
  have hprimary : lower ≤ activation security * (primaryLaw security).weight output := by
    apply le_trans _ (actual_denominator_lower security output)
    dsimp only [lower]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h := RationalDensityInverseProgram.quotient_error
    (RationalFirstResponseProgram.inverse security bits profile output.val : ℝ)
    ((FirstResponse.responseEquiv security).symm (fun color : Palette security => (profile color.val : ℝ)) output)
    ((LocalPairProgram.activationApprox security bits : ℝ) * (primary security bits output.val : ℝ))
    (activation security * (primaryLaw security).weight output) lower
    (RationalFirstResponseProgram.inverseErrorConstant security * bound * (1 / (2 : ℝ)^bits))
    ((1 / 2 + 64 * (Parameters.base security : ℝ) * Parameters.dimension security) * (1 / (2 : ℝ)^bits))
    (RationalDensityInverseProgram.inverseBound security * bound) (by dsimp only [lower]; positivity)
    (approximate_denominator_lower security bits output hfirst) hprimary (by positivity) (by positivity)
    (by unfold RationalDensityInverseProgram.inverseBound; positivity)
    ((RationalFirstResponseProgram.inverse_error security bits profile output bound hb hprofile hfirst).trans_eq (by ring))
    (denominator_error security bits output hprecision hbudget)
    (RationalDensityInverseProgram.actual_inverse_bound security _ bound hb hprofile output)
  rw [current, Rat.cast_div, Rat.cast_mul, actual_formula]
  apply h.trans_eq
  unfold errorConstant lower
  ring_nf
  simp only [inv_inv]
  ring

theorem current_profile_error (security bits : ℕ) (computed : ℕ → ℚ) (profile : Palette security → ℝ)
    (bound profileError : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ profileError)
    (hcomputed : ∀ color : Palette security, |(computed color.val : ℝ)| ≤ bound)
    (hdiff : ∀ color : Palette security, |(computed color.val : ℝ) - profile color| ≤ profileError)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(current security bits computed output.val : ℝ) - actual security profile output| ≤
      errorConstant security * bound * (1 / (2 : ℝ)^bits) + RationalTensorInverseProgram.actualBound security * profileError := by
  exact (abs_sub_le _ (actual security (fun color => (computed color.val : ℝ)) output) _).trans
    (add_le_add (current_error security bits computed bound hb hcomputed hfirst hprecision hbudget output)
      (actual_profile_difference security _ profile profileError he hdiff output))

end
end CurrentAFT.RationalMassLiftProgram

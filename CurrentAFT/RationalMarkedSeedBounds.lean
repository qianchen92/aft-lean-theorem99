import CurrentAFT.RationalMarkedSeedProgram
import CurrentAFT.RationalFiniteMean

/-! # Numerical error of the original marked mixed seed -/
namespace CurrentAFT.RationalMarkedSeedProgram
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls MarkedPairSeed
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw

def primaryErrorConstant (security : ℕ) : ℝ := 64*(Parameters.base security:ℝ)*Parameters.dimension security

def profileBound (security : ℕ) : ℝ := 2*(Parameters.modulus security:ℝ)+1

def meanErrorConstant (security : ℕ) : ℝ := RationalBackgroundDensities.bodyErrorConstant security+
  profileBound security*((Parameters.modulus security:ℝ)*primaryErrorConstant security)

def uniformErrorConstant (security : ℕ) : ℝ := (4*(Parameters.modulus security:ℝ))^2*primaryErrorConstant security

def seedErrorConstant (security : ℕ) : ℝ := RationalBackgroundDensities.bodyErrorConstant security+
  4*meanErrorConstant security+profileBound security*uniformErrorConstant security

def inverseErrorConstant (security : ℕ) : ℝ := RationalDensityInverseProgram.errorConstant security*(5*profileBound security)+
  RationalTensorInverseProgram.actualBound security*seedErrorConstant security

theorem actualSecondCentered_bound (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security) :
    |MarkedPairSeed.secondCentered security scalar primary output| ≤ profileBound security := by
  have hq := FirstResponse.modulus_pos security
  have hl := ActualControls.bodyReference_lower security output
  have hp := ActualControls.bodyReference_positive security output
  have hraw : |MarkedPairSeed.rawDensity security scalar primary output| ≤ 2*(Parameters.modulus security:ℝ) := by
    rw [MarkedPairSeed.rawDensity, abs_div, abs_of_nonneg ((MarkedPairSeed.fixedAnchor security scalar primary).nonneg output), abs_of_pos hp]
    calc
      _ ≤ 1/(bodyReference security).weight output := div_le_div_of_nonneg_right ((MarkedPairSeed.fixedAnchor security scalar primary).atom_le_one output) hp.le
      _ ≤ 1/(1/(2*(Parameters.modulus security:ℝ))) := one_div_le_one_div_of_le (by positivity) hl
      _ = _ := by field_simp
  exact (abs_sub _ _).trans (add_le_add hraw (by norm_num))

theorem secondMean_bound (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security) (output : SafePalette security) :
    |(secondMean security bits scalar.val output.val.val:ℝ)| ≤ profileBound security := by
  rw [secondMean_cast]
  exact CalibrationCoordinateError.expectation_abs_bound _ _ _ (fun color => secondCentered_bound security bits scalar color output)

theorem actualSecondMean_bound (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (output : SafePalette security) :
    |MarkedPairSeed.secondMean security scalar output| ≤ profileBound security :=
  CalibrationCoordinateError.expectation_abs_bound _ _ _ (fun color => actualSecondCentered_bound security scalar color output)

theorem secondMean_error (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(secondMean security bits scalar.val output.val.val:ℝ)-MarkedPairSeed.secondMean security scalar output| ≤
      meanErrorConstant security*(1/(2:ℝ)^bits) := by
  rw [secondMean_cast]
  have hp (color : FirstHistogram.Palette security) :
      |(RationalProposalProgram.approximatePrimaryLaw security bits).weight color-(primaryLaw security).weight color| ≤
      primaryErrorConstant security*(1/(2:ℝ)^bits) := by
    simpa only [RationalProposalProgram.approximatePrimaryLaw, primaryLaw, primaryErrorConstant] using
      RationalProposalProgram.primary_error security bits color hprecision hbudget
  have hx := RationalFiniteMean.expectation_error (primaryLaw security) (RationalProposalProgram.approximatePrimaryLaw security bits)
    (fun color => MarkedPairSeed.secondCentered security scalar color output)
    (fun color => (secondCentered security bits color.val scalar.val output.val.val:ℝ))
    (RationalBackgroundDensities.bodyErrorConstant security*(1/(2:ℝ)^bits))
    (primaryErrorConstant security*(1/(2:ℝ)^bits)) (profileBound security)
    (by unfold primaryErrorConstant; positivity) (by unfold profileBound; positivity)
    (fun color => secondCentered_error security bits scalar color output hprecision hbudget) hp
    (fun color => actualSecondCentered_bound security scalar color output)
  exact hx.trans_eq (by unfold meanErrorConstant; simp only [Fintype.card_fin]; ring)

theorem uniformRelative_bound (security bits : ℕ) (primary : FirstHistogram.Palette security) :
    |(uniformRelative security bits primary.val:ℝ)| ≤ 4 := by
  have hq := FirstResponse.modulus_pos security
  have hl := RationalProposalProgram.primary_lower security bits primary
  have hp : 0 < (RationalProposalProgram.primary security bits primary.val:ℝ) := (by positivity : (0:ℝ)<1/(4*(Parameters.modulus security:ℝ))).trans_le hl
  simp only [uniformRelative, colors, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, PublicParameterProgram.modulus_value]
  rw [abs_div, abs_of_pos (one_div_pos.mpr hq), abs_of_pos hp]
  calc
    _ ≤ (1/(Parameters.modulus security:ℝ))/(1/(4*(Parameters.modulus security:ℝ))) := div_le_div_of_nonneg_left (by positivity) (by positivity) hl
    _ = _ := by field_simp

theorem uniformRelative_error (security bits : ℕ) (primary : FirstHistogram.Palette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(uniformRelative security bits primary.val:ℝ)-MarkedPairSeed.uniformRelative security primary| ≤
      uniformErrorConstant security*(1/(2:ℝ)^bits) := by
  let q : ℝ := Parameters.modulus security
  have hq : 0 < q := FirstResponse.modulus_pos security
  have hq1 : 1 ≤ q := by
    change (1:ℝ) ≤ (Parameters.modulus security:ℝ)
    exact_mod_cast (Nat.succ_le_of_lt (Parameters.modulus_spec security).2.pos)
  have hr : 1/(4*q) ≤ (primaryLaw security).weight primary := by
    apply le_trans _ (show 1/(2*q) ≤ (primaryLaw security).weight primary by simpa only [primaryLaw] using primaryProfile_atom_lower security primary)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have ha := RationalProposalProgram.primary_lower security bits primary
  have hd : |(RationalProposalProgram.primary security bits primary.val:ℝ)-(primaryLaw security).weight primary| ≤ primaryErrorConstant security*(1/(2:ℝ)^bits) := by
    simpa only [primaryLaw, primaryErrorConstant] using RationalProposalProgram.primary_error security bits primary hprecision hbudget
  have hv : |1/q| ≤ 1 := by rw [abs_of_pos (one_div_pos.mpr hq)]; simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq1
  have hx := RationalDensityInverseProgram.quotient_error (1/q) (1/q)
    (RationalProposalProgram.primary security bits primary.val:ℝ) ((primaryLaw security).weight primary)
    (1/(4*q)) 0 (primaryErrorConstant security*(1/(2:ℝ)^bits)) 1 (by positivity) ha hr
    (by norm_num) (by unfold primaryErrorConstant; positivity) (by norm_num) (by simp) hd hv
  simp only [uniformRelative, colors, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, PublicParameterProgram.modulus_value,
    MarkedPairSeed.uniformRelative, FringeCertificate.uniformProfile]
  have he : 0/(1/(4*q))+1*(primaryErrorConstant security*(1/(2:ℝ)^bits))/(1/(4*q))^2 =
      uniformErrorConstant security*(1/(2:ℝ)^bits) := by
    unfold uniformErrorConstant
    dsimp only [q]
    ring_nf
    simp only [inv_inv]
  simpa only [q, one_div] using hx.trans_eq he

theorem seedDensity_bound (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security) :
    |(seedDensity security bits primary.val scalar.val output.val.val:ℝ)| ≤ 5*profileBound security := by
  rw [seedDensity, Rat.cast_sub, Rat.cast_mul]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  exact (add_le_add (secondCentered_bound security bits scalar primary output)
    (mul_le_mul (uniformRelative_bound security bits primary) (secondMean_bound security bits scalar output)
      (abs_nonneg _) (by norm_num))).trans_eq (by unfold profileBound; ring)

theorem seedDensity_error (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(seedDensity security bits primary.val scalar.val output.val.val:ℝ)-MarkedPairSeed.seedDensity security scalar primary output| ≤
      seedErrorConstant security*(1/(2:ℝ)^bits) := by
  let U : ℝ := uniformRelative security bits primary.val
  let V := MarkedPairSeed.uniformRelative security primary
  let M : ℝ := secondMean security bits scalar.val output.val.val
  let N := MarkedPairSeed.secondMean security scalar output
  have hu : |U| ≤ 4 := uniformRelative_bound security bits primary
  have hm : |N| ≤ profileBound security := actualSecondMean_bound security scalar output
  have heU : |U-V| ≤ uniformErrorConstant security*(1/(2:ℝ)^bits) := uniformRelative_error security bits primary hprecision hbudget
  have heM : |M-N| ≤ meanErrorConstant security*(1/(2:ℝ)^bits) := secondMean_error security bits scalar output hprecision hbudget
  have hprod : |U*M-V*N| ≤ (4*meanErrorConstant security+profileBound security*uniformErrorConstant security)*(1/(2:ℝ)^bits) := by
    have hid : U*M-V*N = U*(M-N)+(U-V)*N := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact (add_le_add (mul_le_mul hu heM (abs_nonneg _) (by norm_num))
      (mul_le_mul heU hm (abs_nonneg _) (by unfold uniformErrorConstant primaryErrorConstant; positivity))).trans_eq (by ring)
  have heC := secondCentered_error security bits scalar primary output hprecision hbudget
  simp only [seedDensity, Rat.cast_sub, Rat.cast_mul, MarkedPairSeed.seedDensity]
  change |(secondCentered security bits primary.val scalar.val output.val.val:ℝ)-U*M-
    (MarkedPairSeed.secondCentered security scalar primary output-V*N)| ≤ _
  rw [show (secondCentered security bits primary.val scalar.val output.val.val:ℝ)-U*M-
      (MarkedPairSeed.secondCentered security scalar primary output-V*N) =
    ((secondCentered security bits primary.val scalar.val output.val.val:ℝ)-MarkedPairSeed.secondCentered security scalar primary output)-(U*M-V*N) by ring]
  exact (abs_sub _ _).trans ((add_le_add heC hprod).trans_eq (by unfold seedErrorConstant; ring))

theorem inverseDensity_error (security bits : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : FirstHistogram.Palette security) (output : SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(inverseDensity security bits scalar.val primary.val output.val.val:ℝ)-
      MarkedPairCertificates.inverseDensity security scalar primary output| ≤ inverseErrorConstant security*(1/(2:ℝ)^bits) := by
  let computed : FirstHistogram.Palette security → ℝ := fun color => seedDensity security bits color.val scalar.val output.val.val
  let ideal : FirstHistogram.Palette security → ℝ := fun color => MarkedPairSeed.seedDensity security scalar color output
  have hQ := RationalDensityInverseProgram.current_error security bits
    (fun color => seedDensity security bits color scalar.val output.val.val) primary (5*profileBound security)
    (by unfold profileBound; positivity) (fun color => seedDensity_bound security bits scalar color output) hfirst hprecision hbudget
  have hR := RationalTensorInverseProgram.actual_inverse_bound security (computed-ideal)
    (seedErrorConstant security*(1/(2:ℝ)^bits))
    (by
      unfold seedErrorConstant meanErrorConstant profileBound uniformErrorConstant primaryErrorConstant
        RationalBackgroundDensities.bodyErrorConstant RationalBackgroundDensities.centerErrorConstant
      positivity)
    (fun color => seedDensity_error security bits scalar color output hprecision hbudget) primary
  have hdiff : |PrimaryTensorInverse.densityInverse security computed primary-PrimaryTensorInverse.densityInverse security ideal primary| ≤
      RationalTensorInverseProgram.actualBound security*(seedErrorConstant security*(1/(2:ℝ)^bits)) := by
    simpa only [map_sub, Pi.sub_apply] using hR
  exact (abs_sub_le _ (PrimaryTensorInverse.densityInverse security computed primary) _).trans
    ((add_le_add hQ hdiff).trans_eq (by unfold inverseErrorConstant; ring))

end
end CurrentAFT.RationalMarkedSeedProgram

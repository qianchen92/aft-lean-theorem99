import CurrentAFT.RationalProposalProgram
import CurrentAFT.BinaryPairProgram
import CurrentAFT.FirstResponse

/-! # Rational programs for the actual sign profile and first inverse

All tables use the same current Gaussian approximation and activation as
the proposal. The inverse is the literal rank-one formula, with an exact
rational denominator guard for low precision. No real matrix inverse is
an input to the program.
-/
namespace CurrentAFT.RationalFirstResponseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def profileKernel (colors width : ℕ) (positive : Bool) (blur source : ℤ) (output : ℕ) : ℚ :=
  AFT.V7Calibration.averagedSliceProgram colors 1
    ((if positive then (width : ℤ) else -2*(width : ℤ)+1)+blur) source width output

def profile (security bits : ℕ) (positive : Bool) (output : ℕ) : ℚ :=
  seedEvaluate security bits (fun seed => profileKernel (PublicParameterProgram.modulus security).count
    ((security+2)^48) positive (seed.1.1.val-seed.1.2.val) seed.2.val output)

def signProfile (security bits output : ℕ) : ℚ :=
  (1-LocalPairProgram.activationApprox security bits)*(profile security bits true output-profile security bits false output)

def anchorSign (security color : ℕ) : ℚ :=
  if 2*color < (PublicParameterProgram.modulus security).count-1 then -1
  else if (PublicParameterProgram.modulus security).count-1 < 2*color then 1 else 0

def functional (security : ℕ) (input : ℕ → ℚ) : ℚ :=
  ∑ color : Fin (PublicParameterProgram.modulus security).count, anchorSign security color.val*input color.val

def denominator (security bits : ℕ) : ℚ :=
  LocalPairProgram.activationApprox security bits + functional security (signProfile security bits)

def guardedDenominator (security bits : ℕ) : ℚ :=
  max (denominator security bits) (LocalPairProgram.activationApprox security bits / 4)

def response (security bits : ℕ) (input : ℕ → ℚ) (output : ℕ) : ℚ :=
  input output + functional security input / LocalPairProgram.activationApprox security bits * signProfile security bits output

def inverse (security bits : ℕ) (input : ℕ → ℚ) (output : ℕ) : ℚ :=
  input output - functional security input / guardedDenominator security bits * signProfile security bits output

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  DiffuseProfiles.actualProfile DiffuseProfiles.signProfile DiffuseProfiles.activation

theorem profileKernel_bound (colors width output : ℕ) (positive : Bool) (blur source : ℤ) :
    |(profileKernel colors width positive blur source output : ℝ)| ≤ 1 :=
  AFT.V7Calibration.averagedSliceProgram_abs_le_one _ _ _ _ _ _

theorem profile_cast (security bits : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
    (profile security bits positive output.val : ℝ) =
      DiffuseProfiles.profile (Parameters.modulus security) (Parameters.anchorWidth security) 1 positive
        (approximateSeedLaw security bits) (actualBlur security) (actualSecond security) output := by
  unfold profile
  rw [seedEvaluate_cast, PublicParameterProgram.modulus_value]
  have hw : (security+2)^48 = Parameters.anchorWidth security := by
    simp only [anchorWidth_eq, Parameters.base]
  rw [hw]
  simp only [profileKernel, AFT.V7Calibration.averagedSliceProgram_cast, DiffuseProfiles.profile,
    TrimmedSlice.mixedLaw, FiniteDist.expectation, actualBlur, actualSecond, intervalStart]

theorem profile_ideal (security : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
    (actualSeedLaw security).expectation (fun seed =>
      (profileKernel (Parameters.modulus security) (Parameters.anchorWidth security) positive
        (actualBlur security seed) (actualSecond security seed) output.val : ℝ)) = actualProfile security positive output := by
  simp only [profileKernel, AFT.V7Calibration.averagedSliceProgram_cast, actualProfile, DiffuseProfiles.profile,
    TrimmedSlice.mixedLaw, FiniteDist.expectation, intervalStart]

theorem profile_error (security bits : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
    |(profile security bits positive output.val : ℝ)-actualProfile security positive output| ≤ 3/(2:ℝ)^bits := by
  have hw : (security+2)^48 = Parameters.anchorWidth security := by
    simp only [anchorWidth_eq, Parameters.base]
  have he : (profile security bits positive output.val : ℝ) =
      (approximateSeedLaw security bits).expectation (fun seed =>
        (profileKernel (Parameters.modulus security) (Parameters.anchorWidth security) positive
          (actualBlur security seed) (actualSecond security seed) output.val : ℝ)) := by
    unfold profile
    rw [seedEvaluate_cast, PublicParameterProgram.modulus_value, hw]
    rfl
  calc
    _ = |(approximateSeedLaw security bits).expectation (fun seed =>
        (profileKernel (Parameters.modulus security) (Parameters.anchorWidth security) positive
          (actualBlur security seed) (actualSecond security seed) output.val : ℝ)) -
      (actualSeedLaw security).expectation (fun seed =>
        (profileKernel (Parameters.modulus security) (Parameters.anchorWidth security) positive
          (actualBlur security seed) (actualSecond security seed) output.val : ℝ))| :=
      congrArg abs (congrArg₂ (·-·) he (profile_ideal security positive output).symm)
    _ ≤ _ := (CyclePatternProgram.expectation_difference_le_l1 _ _ _ 1
      (fun seed => profileKernel_bound _ _ _ _ _ _)).trans (by simpa only [one_mul] using seed_l1 security bits)

theorem actualProfile_bound (security : ℕ) (positive : Bool) (output : FirstHistogram.Palette security) :
    |actualProfile security positive output| ≤ 1 := by
  rw [← profile_ideal]
  unfold FiniteDist.expectation
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ seed : ActualSeed security, (actualSeedLaw security).weight seed := by
      apply Finset.sum_le_sum
      intro seed _
      rw [abs_mul, abs_of_nonneg ((actualSeedLaw security).nonneg seed)]
      exact (mul_le_mul_of_nonneg_left (profileKernel_bound _ _ _ _ _ _)
        ((actualSeedLaw security).nonneg seed)).trans_eq (mul_one _)
    _ = 1 := (actualSeedLaw security).sum_one

theorem signProfile_error (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(signProfile security bits output.val : ℝ)-DiffuseProfiles.signProfile security output| ≤ 7/(2:ℝ)^bits := by
  let rate : ℝ := LocalPairProgram.activationApprox security bits
  let first : ℝ := profile security bits true output.val
  let second : ℝ := profile security bits false output.val
  let trueFirst := actualProfile security true output
  let trueSecond := actualProfile security false output
  have hr := LocalPairProgram.activationApprox_bounds security bits
  have hrate : 0 ≤ rate ∧ rate ≤ 1/2 := hr
  have hrem : 0 ≤ 1-rate := by linarith only [hrate.2]
  have hrem' : 1-rate ≤ 1 := by linarith only [hrate.1]
  have he := LocalPairProgram.activationApprox_error security bits
  have hp : |first-trueFirst| ≤ 3/(2:ℝ)^bits := profile_error security bits true output
  have hm : |second-trueSecond| ≤ 3/(2:ℝ)^bits := profile_error security bits false output
  have hd : |(first-trueFirst)-(second-trueSecond)| ≤ 6/(2:ℝ)^bits :=
    (abs_sub _ _).trans ((add_le_add hp hm).trans_eq (by ring))
  have hg : |trueFirst-trueSecond| ≤ 2 :=
    (abs_sub _ _).trans (by linarith only [actualProfile_bound security true output, actualProfile_bound security false output])
  unfold signProfile DiffuseProfiles.signProfile
  simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  change |(1-rate)*(first-second)-(1-DiffuseProfiles.activation security)*(trueFirst-trueSecond)| ≤ _
  calc
    _ = |(1-rate)*((first-trueFirst)-(second-trueSecond)) +
        (DiffuseProfiles.activation security-rate)*(trueFirst-trueSecond)| := by congr 1; ring
    _ ≤ |(1-rate)*((first-trueFirst)-(second-trueSecond))| +
        |(DiffuseProfiles.activation security-rate)*(trueFirst-trueSecond)| := abs_add_le _ _
    _ = (1-rate)*|(first-trueFirst)-(second-trueSecond)| +
        |rate-DiffuseProfiles.activation security| * |trueFirst-trueSecond| := by
      rw [abs_mul, abs_of_nonneg hrem, abs_mul, abs_sub_comm (DiffuseProfiles.activation security) rate]
    _ ≤ 1*(6/(2:ℝ)^bits)+((1/2:ℝ)*(1/(2:ℝ)^bits))*2 :=
      add_le_add (mul_le_mul hrem' hd (abs_nonneg _) (by positivity))
        (mul_le_mul he hg (abs_nonneg _) (by positivity))
    _ = _ := by ring

theorem anchorSign_cast (security : ℕ) (color : FirstHistogram.Palette security) :
    (anchorSign security color.val : ℝ) = FirstResponse.anchorSign security color := by
  unfold anchorSign FirstResponse.anchorSign
  rw [PublicParameterProgram.modulus_value]
  split_ifs <;> norm_num

theorem functional_cast (security : ℕ) (input : ℕ → ℚ) :
    (functional security input : ℝ) =
      AFT.signFunctional (FirstResponse.anchorSign security) (fun color : FirstHistogram.Palette security => (input color.val : ℝ)) := by
  simp only [functional, Rat.cast_sum, Rat.cast_mul]
  rw [PublicParameterProgram.modulus_value]
  simp only [anchorSign_cast, AFT.signFunctional]

def actualDenominator (security : ℕ) : ℝ := DiffuseProfiles.activation security +
  AFT.signFunctional (FirstResponse.anchorSign security) (DiffuseProfiles.signProfile security)

theorem denominator_error (security bits : ℕ) :
    |(denominator security bits : ℝ)-actualDenominator security| ≤
      (8*(Parameters.modulus security:ℝ)+1)/(2:ℝ)^bits := by
  have ha := LocalPairProgram.activationApprox_error security bits
  have hs : |AFT.signFunctional (FirstResponse.anchorSign security)
      (fun color => (signProfile security bits color.val : ℝ))-
      AFT.signFunctional (FirstResponse.anchorSign security) (DiffuseProfiles.signProfile security)| ≤
      (Parameters.modulus security:ℝ)*(7/(2:ℝ)^bits) := by
    unfold AFT.signFunctional
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _color : FirstHistogram.Palette security, 7/(2:ℝ)^bits := by
        apply Finset.sum_le_sum
        intro color _
        rw [← mul_sub, abs_mul]
        exact (mul_le_mul (FirstResponse.anchorSign_abs_le_one security color)
          (signProfile_error security bits color) (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
      _ = _ := by simp
  unfold denominator actualDenominator
  rw [Rat.cast_add, functional_cast]
  calc
    _ = |((LocalPairProgram.activationApprox security bits : ℝ)-DiffuseProfiles.activation security) +
        (AFT.signFunctional (FirstResponse.anchorSign security) (fun color => (signProfile security bits color.val : ℝ))-
          AFT.signFunctional (FirstResponse.anchorSign security) (DiffuseProfiles.signProfile security))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add ha hs)
    _ = ((1/2:ℝ)+7*Parameters.modulus security)/(2:ℝ)^bits := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by have hq := FirstResponse.modulus_pos security; linarith) (by positivity)

theorem guardedDenominator_pos (security bits : ℕ) : 0 < (guardedDenominator security bits : ℝ) := by
  have ha := RationalProposalProgram.activationApprox_pos security bits
  unfold guardedDenominator
  rw [Rat.cast_max, Rat.cast_div, Rat.cast_ofNat]
  exact (div_pos ha (by norm_num)).trans_le (le_max_right _ _)

def PrecisionBudget (security bits : ℕ) : Prop :=
  (8*(Parameters.modulus security:ℝ)+2)*(1/(2:ℝ)^bits) ≤ 1/(16*(Parameters.base security:ℝ))

theorem denominator_lower (security bits : ℕ) (hprecision : PrecisionBudget security bits) :
    1/(16*(Parameters.base security:ℝ)) ≤ (denominator security bits : ℝ) := by
  have hb := FirstResponse.base_pos security
  have ha := FirstResponse.activation_lower_simple security
  have hd := FirstResponse.inverse_denominator_lower security
  change DiffuseProfiles.activation security/2 ≤ actualDenominator security at hd
  have he := denominator_error security bits
  have he' : |(denominator security bits : ℝ)-actualDenominator security| ≤
      (8*(Parameters.modulus security:ℝ)+1)*(1/(2:ℝ)^bits) := he.trans_eq (by ring)
  have hprec : (8*(Parameters.modulus security:ℝ)+2)*(1/(2:ℝ)^bits) ≤
      1/(16*(Parameters.base security:ℝ)) := hprecision
  have hal : 1/(8*(Parameters.base security:ℝ)) ≤ actualDenominator security :=
    (show 1/(8*(Parameters.base security:ℝ)) ≤ DiffuseProfiles.activation security/2 by
      convert div_le_div_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 2) using 1; ring).trans hd
  have hlow := (abs_le.mp he').1
  have heps : 0 ≤ 1/(2:ℝ)^bits := by positivity
  have hscale : 1/(8*(Parameters.base security:ℝ)) = 2*(1/(16*(Parameters.base security:ℝ))) := by ring
  nlinarith only [hal, hlow, hprec, heps, hscale]

theorem guardedDenominator_eq (security bits : ℕ) (hprecision : PrecisionBudget security bits) :
    guardedDenominator security bits = denominator security bits := by
  have hd := FirstResponse.inverse_denominator_lower security
  change DiffuseProfiles.activation security/2 ≤ actualDenominator security at hd
  have ha := FirstResponse.activation_lower_simple security
  have hal : 1/(16*(Parameters.base security:ℝ)) ≤ DiffuseProfiles.activation security/4 := by
    convert div_le_div_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 4) using 1
    ring
  have he := denominator_error security bits
  have he' : |(denominator security bits : ℝ)-actualDenominator security| ≤
      (8*(Parameters.modulus security:ℝ)+1)*(1/(2:ℝ)^bits) := he.trans_eq (by ring)
  have hae := LocalPairProgram.activationApprox_error security bits
  have hprec : (8*(Parameters.modulus security:ℝ)+2)*(1/(2:ℝ)^bits) ≤
      1/(16*(Parameters.base security:ℝ)) := hprecision
  have hguard : (LocalPairProgram.activationApprox security bits : ℝ)/4 ≤ (denominator security bits : ℝ) := by
    have hlow := (abs_le.mp he').1
    have hhigh := (abs_le.mp hae).2
    have heps : 0 ≤ 1/(2:ℝ)^bits := by positivity
    nlinarith only [hd, hal, hprec, hlow, hhigh, heps]
  have hguardQ : LocalPairProgram.activationApprox security bits/4 ≤ denominator security bits := by
    exact_mod_cast hguard
  exact max_eq_left hguardQ

theorem actualDenominator_lower (security : ℕ) :
    1/(16*(Parameters.base security:ℝ)) ≤ actualDenominator security := by
  have ha := FirstResponse.activation_lower_simple security
  have hd := FirstResponse.inverse_denominator_lower security
  change DiffuseProfiles.activation security/2 ≤ actualDenominator security at hd
  have hal : 1/(8*(Parameters.base security:ℝ)) ≤ DiffuseProfiles.activation security/2 := by
    convert div_le_div_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 2) using 1
    ring
  apply le_trans _ (hal.trans hd)
  exact one_div_le_one_div_of_le (by have hb := FirstResponse.base_pos security; positivity) (by
    have hb := FirstResponse.base_pos security; nlinarith)

theorem functional_bound (security : ℕ) (input : ℕ → ℚ) (bound : ℝ) (_hbound : 0 ≤ bound)
    (hinput : ∀ color : FirstHistogram.Palette security, |(input color.val : ℝ)| ≤ bound) :
    |(functional security input : ℝ)| ≤ (Parameters.modulus security:ℝ)*bound := by
  rw [functional_cast]
  unfold AFT.signFunctional
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _color : FirstHistogram.Palette security, bound := by
      apply Finset.sum_le_sum
      intro color _
      rw [abs_mul]
      exact (mul_le_mul (FirstResponse.anchorSign_abs_le_one security color) (hinput color)
        (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by simp

theorem actualSignProfile_bound (security : ℕ) (color : FirstHistogram.Palette security) :
    |DiffuseProfiles.signProfile security color| ≤ 2 := by
  have ha := DiffuseProfiles.activation_pos security
  have hu := DiffuseProfiles.activation_le_half security
  unfold DiffuseProfiles.signProfile
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-DiffuseProfiles.activation security)]
  have hgap : |actualProfile security true color - actualProfile security false color| ≤ 2 :=
    (abs_sub _ _).trans ((add_le_add (actualProfile_bound security true color)
      (actualProfile_bound security false color)).trans_eq (by norm_num))
  exact (mul_le_mul (by linarith : 1-DiffuseProfiles.activation security ≤ 1)
    hgap (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by norm_num)

def inverseErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security:ℝ)*(112*(Parameters.base security:ℝ)+
    512*(Parameters.base security:ℝ)^2*(8*(Parameters.modulus security:ℝ)+1))

theorem inverse_error (security bits : ℕ) (input : ℕ → ℚ) (output : FirstHistogram.Palette security)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hinput : ∀ color : FirstHistogram.Palette security, |(input color.val : ℝ)| ≤ bound)
    (hprecision : PrecisionBudget security bits) :
    |(inverse security bits input output.val : ℝ) -
      (FirstResponse.responseEquiv security).symm
        (fun color : FirstHistogram.Palette security => (input color.val : ℝ)) output| ≤
      inverseErrorConstant security*bound/(2:ℝ)^bits := by
  let d : ℝ := actualDenominator security
  let a : ℝ := denominator security bits
  let r : ℝ := DiffuseProfiles.signProfile security output
  let s : ℝ := signProfile security bits output.val
  let f : ℝ := functional security input
  let base : ℝ := Parameters.base security
  let epsilon : ℝ := 1/(2:ℝ)^bits
  have hb : 0 < base := FirstResponse.base_pos security
  have hlo : 0 < 1/(16*base) := by positivity
  have ha : 1/(16*base) ≤ a := denominator_lower security bits hprecision
  have hd : 1/(16*base) ≤ d := actualDenominator_lower security
  have ha0 : 0 < a := hlo.trans_le ha
  have hd0 : 0 < d := hlo.trans_le hd
  have hai : a⁻¹ ≤ 16*base := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hlo ha
  have hdi : d⁻¹ ≤ 16*base := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hlo hd
  have he : |a-d| ≤ (8*(Parameters.modulus security:ℝ)+1)*epsilon :=
    (denominator_error security bits).trans_eq (by dsimp only [epsilon]; ring)
  have hr : |r| ≤ 2 := actualSignProfile_bound security output
  have hs : |s-r| ≤ 7*epsilon := (signProfile_error security bits output).trans_eq (by dsimp only [epsilon]; ring)
  have hf : |f| ≤ (Parameters.modulus security:ℝ)*bound := functional_bound security input bound hbound hinput
  have hrecip : |a⁻¹-d⁻¹| ≤ 256*base^2*((8*(Parameters.modulus security:ℝ)+1)*epsilon) := by
    calc
      _ = |(d-a)*(a⁻¹*d⁻¹)| := by congr 1; field_simp
      _ = |a-d| * (a⁻¹*d⁻¹) := by
        rw [abs_mul, abs_sub_comm d a, abs_of_pos (mul_pos (inv_pos.mpr ha0) (inv_pos.mpr hd0))]
      _ ≤ ((8*(Parameters.modulus security:ℝ)+1)*epsilon)*((16*base)*(16*base)) :=
        mul_le_mul he (mul_le_mul hai hdi (inv_nonneg.mpr hd0.le) (by positivity))
          (mul_nonneg (inv_nonneg.mpr ha0.le) (inv_nonneg.mpr hd0.le)) (by positivity)
      _ = _ := by ring
  have hratio : |s*a⁻¹-r*d⁻¹| ≤ 7*epsilon*(16*base) +
      2*(256*base^2*((8*(Parameters.modulus security:ℝ)+1)*epsilon)) := by
    calc
      _ = |(s-r)*a⁻¹+r*(a⁻¹-d⁻¹)| := by congr 1; ring
      _ ≤ |(s-r)*a⁻¹|+|r*(a⁻¹-d⁻¹)| := abs_add_le _ _
      _ = |s-r| * a⁻¹+|r| * |a⁻¹-d⁻¹| := by rw [abs_mul, abs_of_pos (inv_pos.mpr ha0), abs_mul]
      _ ≤ _ := add_le_add (mul_le_mul hs hai (inv_nonneg.mpr ha0.le) (by positivity))
        (mul_le_mul hr hrecip (abs_nonneg _) (by norm_num))
  have hformula : (inverse security bits input output.val : ℝ) -
      (FirstResponse.responseEquiv security).symm
        (fun color : FirstHistogram.Palette security => (input color.val : ℝ)) output =
      -f*(s*a⁻¹-r*d⁻¹) := by
    rw [FirstResponse.response_inverse_formula]
    simp only [inverse, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, guardedDenominator_eq security bits hprecision,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← functional_cast]
    change (input output.val:ℝ)-f/a*s - ((input output.val:ℝ)-d⁻¹*f*r) = _
    ring
  rw [hformula, abs_mul, abs_neg]
  calc
    _ ≤ ((Parameters.modulus security:ℝ)*bound)*(7*epsilon*(16*base) +
        2*(256*base^2*((8*(Parameters.modulus security:ℝ)+1)*epsilon))) :=
      mul_le_mul hf hratio (abs_nonneg _) (by have hq := FirstResponse.modulus_pos security; positivity)
    _ = _ := by unfold inverseErrorConstant; dsimp only [base, epsilon]; ring

def sufficientBits (security : ℕ) : ℕ :=
  16*Parameters.base security*(8*(131072*Parameters.base security^64)+2)

attribute [local irreducible] sufficientBits

private theorem precision_of_size (base colors upper bits : ℕ) (hb : 0 < base) (hq : colors ≤ upper)
    (hbits : 16*base*(8*upper+2) ≤ bits) :
    (8*(colors:ℝ)+2)*(1/(2:ℝ)^bits) ≤ 1/(16*(base:ℝ)) := by
  have hn : 16*base*(8*colors+2) ≤ 2^bits := by
    calc
      _ ≤ 16*base*(8*upper+2) := Nat.mul_le_mul_left (16*base) (by omega)
      _ ≤ bits := hbits
      _ ≤ 2^bits := (Nat.lt_two_pow_self (n := bits)).le
  have hreal : 16*(base:ℝ)*(8*(colors:ℝ)+2) ≤ (2:ℝ)^bits := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).mpr hn
  have hbR : (0:ℝ) < base := Nat.cast_pos.mpr hb
  apply (le_div_iff₀ (by positivity : (0:ℝ)<16*base)).mpr
  calc
    _ = (16*(base:ℝ)*(8*(colors:ℝ)+2))/(2:ℝ)^bits := by ring
    _ ≤ 1 := (div_le_one (by positivity : (0:ℝ)<(2:ℝ)^bits)).mpr hreal

theorem precisionBudget_of_sufficientBits (security bits : ℕ) (hbits : sufficientBits security ≤ bits) :
    PrecisionBudget security bits :=
  precision_of_size (Parameters.base security) (Parameters.modulus security)
    (131072*Parameters.base security^64) bits (Parameters.base_pos security)
    (Parameters.modulus_bounds security).2 (by simpa only [sufficientBits] using hbits)

noncomputable def sufficientBitsPolynomial : Polynomial ℕ :=
  16*(Polynomial.X+2)*(8*(131072*(Polynomial.X+2)^64)+2)

theorem sufficientBitsPolynomial_eval (security : ℕ) :
    sufficientBitsPolynomial.eval security = sufficientBits security := by
  simp only [sufficientBitsPolynomial, sufficientBits, Parameters.base, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]

end
end CurrentAFT.RationalFirstResponseProgram

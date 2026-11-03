import CurrentAFT.RationalFirstResponseProgram
import CurrentAFT.PrimaryTensorInverse

/-! # The actual primary inverse including activation and reference whitening -/
namespace CurrentAFT.RationalDensityInverseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current (security bits : ℕ) (score : ℕ → ℚ) (output : ℕ) : ℚ :=
  RationalFirstResponseProgram.inverse security bits
    (fun color => primary security bits color*score color) output /
    (LocalPairProgram.activationApprox security bits*primary security bits output)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw

def inverseBound (security : ℕ) : ℝ := 1+32*(Parameters.base security:ℝ)*Parameters.modulus security

theorem actual_inverse_bound (security : ℕ) (profile : FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hprofile : ∀ color, |profile color| ≤ bound)
    (output : FirstHistogram.Palette security) :
    |(FirstResponse.responseEquiv security).symm profile output| ≤ inverseBound security*bound := by
  have hfunctional : |signFunctional (FirstResponse.anchorSign security) profile| ≤
      (Parameters.modulus security:ℝ)*bound := by
    apply (signFunctional_abs_le_l1 _ _ (FirstResponse.anchorSign_abs_le_one security)).trans
    calc
      _ ≤ ∑ _color : FirstHistogram.Palette security, bound := Finset.sum_le_sum (fun color _ => hprofile color)
      _ = _ := by simp
  have hlo := RationalFirstResponseProgram.actualDenominator_lower security
  have hb0 := FirstResponse.base_pos security
  have hpos : 0 < RationalFirstResponseProgram.actualDenominator security :=
    (by positivity : (0:ℝ)<1/(16*(Parameters.base security:ℝ))).trans_le hlo
  have hinv : (RationalFirstResponseProgram.actualDenominator security)⁻¹ ≤ 16*(Parameters.base security:ℝ) := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le
      (by positivity : (0:ℝ)<1/(16*(Parameters.base security:ℝ))) hlo
  rw [FirstResponse.response_inverse_formula]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ |profile output| +
        |(RationalFirstResponseProgram.actualDenominator security)⁻¹ *
          signFunctional (FirstResponse.anchorSign security) profile * DiffuseProfiles.signProfile security output| := abs_sub _ _
    _ = |profile output| + (RationalFirstResponseProgram.actualDenominator security)⁻¹ *
        |signFunctional (FirstResponse.anchorSign security) profile| * |DiffuseProfiles.signProfile security output| := by
      simp only [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
    _ ≤ bound+(16*(Parameters.base security:ℝ))*((Parameters.modulus security:ℝ)*bound)*2 :=
      add_le_add (hprofile output)
        (mul_le_mul (mul_le_mul hinv hfunctional (abs_nonneg _) (by positivity))
          (RationalFirstResponseProgram.actualSignProfile_bound security output) (abs_nonneg _) (by positivity))
    _ = _ := by unfold inverseBound; ring

theorem quotient_error (u v a b lower numeratorError denominatorError bound : ℝ)
    (hl : 0 < lower) (ha : lower ≤ a) (hb : lower ≤ b)
    (hen : 0 ≤ numeratorError) (hed : 0 ≤ denominatorError) (hbound : 0 ≤ bound)
    (hn : |u-v| ≤ numeratorError) (hd : |a-b| ≤ denominatorError) (hv : |v| ≤ bound) :
    |u/a-v/b| ≤ numeratorError/lower + bound*denominatorError/lower^2 := by
  have ha0 := hl.trans_le ha
  have hb0 := hl.trans_le hb
  have hai : a⁻¹ ≤ lower⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hl ha
  have hbi : b⁻¹ ≤ lower⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hl hb
  have hi : |a⁻¹-b⁻¹| ≤ denominatorError*lower⁻¹^2 := by
    calc
      _ = |(b-a)*(a⁻¹*b⁻¹)| := by congr 1; field_simp
      _ = |a-b| * (a⁻¹*b⁻¹) := by
        rw [abs_mul, abs_sub_comm b a, abs_of_pos (mul_pos (inv_pos.mpr ha0) (inv_pos.mpr hb0))]
      _ ≤ denominatorError*(lower⁻¹*lower⁻¹) :=
        mul_le_mul hd (mul_le_mul hai hbi (inv_nonneg.mpr hb0.le) (inv_nonneg.mpr hl.le))
          (mul_nonneg (inv_nonneg.mpr ha0.le) (inv_nonneg.mpr hb0.le)) hed
      _ = _ := by ring
  calc
    _ = |(u-v)*a⁻¹+v*(a⁻¹-b⁻¹)| := by congr 1; ring
    _ ≤ |(u-v)*a⁻¹|+|v*(a⁻¹-b⁻¹)| := abs_add_le _ _
    _ = |u-v| * a⁻¹+|v| * |a⁻¹-b⁻¹| := by rw [abs_mul, abs_of_pos (inv_pos.mpr ha0), abs_mul]
    _ ≤ numeratorError*lower⁻¹+bound*(denominatorError*lower⁻¹^2) :=
      add_le_add (mul_le_mul hn hai (inv_nonneg.mpr ha0.le) hen)
        (mul_le_mul hv hi (abs_nonneg _) hbound)
    _ = _ := by ring

theorem activationApprox_lower (security bits : ℕ)
    (hprecision : RationalFirstResponseProgram.PrecisionBudget security bits) :
    1/(8*(Parameters.base security:ℝ)) ≤ (LocalPairProgram.activationApprox security bits:ℝ) := by
  have ha := FirstResponse.activation_lower_simple security
  have he := LocalPairProgram.activationApprox_error security bits
  have hp : (8*(Parameters.modulus security:ℝ)+2)*(1/(2:ℝ)^bits) ≤
      1/(16*(Parameters.base security:ℝ)) := hprecision
  have hq := FirstResponse.modulus_pos security
  have hl := (abs_le.mp he).1
  have h0 : 0 ≤ 1/(2:ℝ)^bits := by positivity
  have hscale : 1/(4*(Parameters.base security:ℝ)) = 4*(1/(16*(Parameters.base security:ℝ))) := by ring
  have hscale' : 1/(8*(Parameters.base security:ℝ)) = 2*(1/(16*(Parameters.base security:ℝ))) := by ring
  nlinarith only [ha, hp, hq, hl, h0, hscale, hscale']

def errorConstant (security : ℕ) : ℝ :=
  let base : ℝ := Parameters.base security
  let q : ℝ := Parameters.modulus security
  let coefficient : ℝ := 64*base*Parameters.dimension security
  (32*base*q)*(RationalFirstResponseProgram.inverseErrorConstant security+inverseBound security*coefficient) +
    inverseBound security*(32*base*q)^2*(1/2+coefficient)

theorem current_error (security bits : ℕ) (score : ℕ → ℚ) (output : FirstHistogram.Palette security)
    (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val:ℝ)| ≤ bound)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ))) :
    |(current security bits score output.val:ℝ)-PrimaryTensorInverse.densityInverse security
      (fun color : FirstHistogram.Palette security => (score color.val:ℝ)) output| ≤
      errorConstant security*bound/(2:ℝ)^bits := by
  let epsilon : ℝ := 1/(2:ℝ)^bits
  let base : ℝ := Parameters.base security
  let q : ℝ := Parameters.modulus security
  let coefficient : ℝ := 64*base*Parameters.dimension security
  let approximate : ℕ → ℚ := fun color => primary security bits color*score color
  let realProfile : FirstHistogram.Palette security → ℝ :=
    fun color => (ProposalPrimary.primaryLaw security).weight color*(score color.val:ℝ)
  let approximateProfile : FirstHistogram.Palette security → ℝ := fun color => (approximate color.val:ℝ)
  let middle := (FirstResponse.responseEquiv security).symm approximateProfile output
  let realNumerator := (FirstResponse.responseEquiv security).symm realProfile output
  let approximateNumerator : ℝ := RationalFirstResponseProgram.inverse security bits approximate output.val
  let a : ℝ := (LocalPairProgram.activationApprox security bits:ℝ)*(primary security bits output.val:ℝ)
  let b : ℝ := DiffuseProfiles.activation security*(ProposalPrimary.primaryLaw security).weight output
  let lower : ℝ := 1/(32*base*q)
  have hq : 0 < q := FirstResponse.modulus_pos security
  have hbase : 0 < base := FirstResponse.base_pos security
  have he : 0 ≤ epsilon := by positivity
  have hc : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have hk : 0 ≤ inverseBound security := by unfold inverseBound; positivity
  have hi : 0 ≤ RationalFirstResponseProgram.inverseErrorConstant security := by
    unfold RationalFirstResponseProgram.inverseErrorConstant; positivity
  have hp (color : FirstHistogram.Palette security) :
      |(primary security bits color.val:ℝ)-(ProposalPrimary.primaryLaw security).weight color| ≤ coefficient*epsilon := by
    simpa only [ProposalPrimary.primaryLaw] using RationalProposalProgram.primary_error security bits color hprecision hbudget
  have haProfile (color : FirstHistogram.Palette security) : |approximateProfile color| ≤ bound := by
    dsimp only [approximateProfile, approximate]
    rw [Rat.cast_mul]
    have hc0 : 0 ≤ (primary security bits color.val:ℝ) := (approximatePrimaryLaw security bits).nonneg color
    rw [abs_mul, abs_of_nonneg hc0]
    exact (mul_le_mul ((approximatePrimaryLaw security bits).atom_le_one color) (hscore color)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hrProfile (color : FirstHistogram.Palette security) : |realProfile color| ≤ bound := by
    rw [abs_mul, abs_of_nonneg ((ProposalPrimary.primaryLaw security).nonneg color)]
    exact (mul_le_mul ((ProposalPrimary.primaryLaw security).atom_le_one color) (hscore color)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hdProfile (color : FirstHistogram.Palette security) : |approximateProfile color-realProfile color| ≤ coefficient*epsilon*bound := by
    dsimp only [approximateProfile, approximate, realProfile]
    rw [Rat.cast_mul]
    rw [← sub_mul, abs_mul]
    exact mul_le_mul (hp color) (hscore color) (abs_nonneg _) (mul_nonneg hc he)
  have hn1 : |approximateNumerator-middle| ≤ RationalFirstResponseProgram.inverseErrorConstant security*bound*epsilon :=
    (RationalFirstResponseProgram.inverse_error security bits approximate output bound hb haProfile hfirst).trans_eq (by dsimp only [epsilon]; ring)
  have hn2 : |middle-realNumerator| ≤ inverseBound security*(coefficient*epsilon*bound) := by
    have h := actual_inverse_bound security (approximateProfile-realProfile) (coefficient*epsilon*bound)
      (by positivity) hdProfile output
    simpa only [map_sub, Pi.sub_apply] using h
  have hn : |approximateNumerator-realNumerator| ≤
      (RationalFirstResponseProgram.inverseErrorConstant security+inverseBound security*coefficient)*bound*epsilon :=
    (abs_sub_le _ middle _).trans ((add_le_add hn1 hn2).trans_eq (by ring))
  have hnum : |realNumerator| ≤ inverseBound security*bound := actual_inverse_bound security realProfile bound hb hrProfile output
  have hpa := primary_lower security bits output
  have hpr : 1/(2*q) ≤ (ProposalPrimary.primaryLaw security).weight output := by
    simpa only [ProposalPrimary.primaryLaw] using ProposalPrimary.primaryProfile_atom_lower security output
  have haa := activationApprox_lower security bits hfirst
  have har := FirstResponse.activation_lower_simple security
  have hap0 : 0 ≤ (primary security bits output.val:ℝ) := (approximatePrimaryLaw security bits).nonneg output
  have hpr0 := (ProposalPrimary.primaryLaw security).nonneg output
  have har0 := (DiffuseProfiles.activation_pos security).le
  have hal : lower ≤ a := by
    convert mul_le_mul haa hpa (by positivity) (LocalPairProgram.activationApprox_bounds security bits).1 using 1
    dsimp only [lower, base, q, a]
    ring
  have hbl : lower ≤ b := by
    have hm := mul_le_mul har hpr (by positivity) (DiffuseProfiles.activation_pos security).le
    apply le_trans _ hm
    dsimp only [lower]
    have hprod : (1/(4*(Parameters.base security:ℝ)))*(1/(2*q)) = 1/(8*base*q) := by dsimp only [base]; ring
    rw [hprod]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hden : |a-b| ≤ (1/2+coefficient)*epsilon := by
    have herr := LocalPairProgram.activationApprox_error security bits
    have hrate : |DiffuseProfiles.activation security| ≤ 1 := by
      rw [abs_of_pos (DiffuseProfiles.activation_pos security)]
      exact (DiffuseProfiles.activation_le_half security).trans (by norm_num)
    calc
      _ = |((LocalPairProgram.activationApprox security bits:ℝ)-DiffuseProfiles.activation security)*
          (primary security bits output.val:ℝ) + DiffuseProfiles.activation security*
          ((primary security bits output.val:ℝ)-(ProposalPrimary.primaryLaw security).weight output)| := by
        dsimp only [a, b]; congr 1; ring
      _ ≤ |(LocalPairProgram.activationApprox security bits:ℝ)-DiffuseProfiles.activation security| *
          (primary security bits output.val:ℝ) + |DiffuseProfiles.activation security| *
          |(primary security bits output.val:ℝ)-(ProposalPrimary.primaryLaw security).weight output| := by
        simpa only [abs_mul, abs_of_nonneg hap0] using abs_add_le
          (((LocalPairProgram.activationApprox security bits:ℝ)-DiffuseProfiles.activation security)*(primary security bits output.val:ℝ))
          (DiffuseProfiles.activation security*((primary security bits output.val:ℝ)-(ProposalPrimary.primaryLaw security).weight output))
      _ ≤ ((1/2:ℝ)*epsilon)*1 + 1*(coefficient*epsilon) :=
        add_le_add (mul_le_mul herr ((approximatePrimaryLaw security bits).atom_le_one output) hap0 (by positivity))
          (mul_le_mul hrate (hp output) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hquot := quotient_error approximateNumerator realNumerator a b lower
    ((RationalFirstResponseProgram.inverseErrorConstant security+inverseBound security*coefficient)*bound*epsilon)
    ((1/2+coefficient)*epsilon) (inverseBound security*bound)
    (by dsimp only [lower]; positivity) hal hbl (by positivity) (by positivity) (by positivity) hn hden hnum
  have hformula : (current security bits score output.val:ℝ)-PrimaryTensorInverse.densityInverse security
      (fun color : FirstHistogram.Palette security => (score color.val:ℝ)) output = approximateNumerator/a-realNumerator/b := by
    simp only [current, Rat.cast_div, Rat.cast_mul, PrimaryTensorInverse.densityInverse_apply]
    change approximateNumerator/a - (DiffuseProfiles.activation security)⁻¹*realNumerator/
      (ProposalPrimary.primaryLaw security).weight output = _
    dsimp only [b]
    ring
  rw [hformula]
  apply hquot.trans_eq
  dsimp only [lower, base, q, coefficient, epsilon, errorConstant]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  ring_nf
  simp only [inv_inv]
  ring

end
end CurrentAFT.RationalDensityInverseProgram

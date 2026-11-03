import AFT.ActualSliceMeanProgram
import AFT.ActualActivationProgram

/-! # Rational evaluation of the actual base-primary calibration -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualLegPopulationProgram (n : ℕ) : ℕ := (max 2 n)^30

def actualDimensionProgram (n : ℕ) : ℕ := (ParameterProgram.modulus n).value*(max 2 n)^20

/-- The formula is rearranged before approximation, so that only the
already-controlled activation reciprocal is divided numerically. -/
def actualBasePrimaryProgram (constant n : ℕ) (color : ℤ) : ℚ :=
  actualActivationInverseApprox constant n n*
    ((actualDimensionProgram n : ℚ)/((actualLegPopulationProgram n : ℚ)*(ParameterProgram.modulus n).value)-
      (actualRootPopulationProgram n : ℚ)/actualLegPopulationProgram n*actualBodyMeanProgram constant n color-
      2*actualFairSliceProgram constant n true color)+
    2*actualFairSliceProgram constant n false color-actualBodyMeanProgram constant n color

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem actualLegPopulationProgram_eq (n : ℕ) : actualLegPopulationProgram n=Parameters.legs n := rfl

theorem actualDimensionProgram_eq (n : ℕ) : actualDimensionProgram n=Parameters.dimension n := by
  unfold actualDimensionProgram
  rw [ParameterProgram.modulus_value]
  rfl

def actualFairSliceMean (constant : ℝ) (n : ℕ) (shifted : Bool) (color : ℤ) : ℝ :=
  TrimmedSlice.fairMixedLaw (Parameters.modulus n) (boundaryHalf constant n)
    (startsPlus constant n) (startsMinus constant n)
    (if shifted then pairSourceShift constant n else fun _ => 0)
    (pairSourceLaw constant n).weight (Parameters.anchorWidth n) color

def actualSafeBodyMean (constant : ℝ) (n : ℕ) (color : ℤ) : ℝ :=
  TrimmedSlice.blurredSafeLaw (Parameters.modulus n) (Parameters.safeMargin n)
    (bodyShift constant n) (bodyBlur constant n).weight color

theorem actualSafeBodyMean_abs_le_one (constant : ℝ) (n : ℕ) (color : ℤ) :
    |actualSafeBodyMean constant n color|≤1 := by
  unfold actualSafeBodyMean TrimmedSlice.blurredSafeLaw
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ sample,(bodyBlur constant n).weight sample := by
      apply Finset.sum_le_sum
      intro sample _
      rw [abs_mul,abs_of_nonneg ((bodyBlur constant n).nonneg sample)]
      have hh := intervalProbabilityProgram_abs_le_one (Parameters.safeMargin n)
        ((Parameters.modulus n : ℤ)-2*Parameters.safeMargin n).toNat (color-bodyShift constant n sample)
      rw [intervalProbabilityProgram_cast] at hh
      exact mul_le_of_le_one_right ((bodyBlur constant n).nonneg sample) hh
    _ = 1 := (bodyBlur constant n).sum_one

theorem actualFairSliceMean_abs_le_one (constant : ℝ) (n : ℕ) (shifted : Bool) (color : ℤ) :
    |actualFairSliceMean constant n shifted color|≤1 := fair_slice_abs_le_one _ _ _ _ _ _ _ _

theorem basePrimary_scalar_rearrange (dimension bodies legs activation uniform body shifted unshifted : ℝ)
    (hlegs : legs≠0) (hactivation : activation≠0) :
    (dimension*uniform-(bodies+legs*activation)*body-2*legs*shifted+2*legs*activation*unshifted)/
      (legs*activation)=activation⁻¹*(dimension/legs*uniform-bodies/legs*body-2*shifted)+2*unshifted-body := by
  field_simp
  ring

theorem actualBasePrimary_rearrange (constant : ℝ) (n : ℕ) (hc : 1≤constant) (hn : 1≤n)
    (color : Fin (Parameters.modulus n)) :
    basePrimary n constant (boundaryHalf constant n) (bodyShift constant n) (bodyBlur constant n)
      (startsPlus constant n) (startsMinus constant n) (pairSourceShift constant n) (pairSourceLaw constant n) color=
      (v7Activation constant n)⁻¹*
        ((Parameters.dimension n : ℝ)/((Parameters.legs n : ℝ)*Parameters.modulus n)-
          (Parameters.bodies n : ℝ)/Parameters.legs n*actualSafeBodyMean constant n color.val-
          2*actualFairSliceMean constant n true color.val)+
        2*actualFairSliceMean constant n false color.val-actualSafeBodyMean constant n color.val := by
  have hm : (Parameters.legs n : ℝ)≠0 := by
    have hx := Parameters.security_ge_two n
    unfold Parameters.legs
    positivity
  have ha : v7Activation constant n≠0 := ne_of_gt (activation_positive _ _ _ _
    (legFeatureCount_positive constant n hc hn))
  unfold basePrimary TrimmedSlice.actualFairBasePrimary basePrimaryProfile
  rw [basePrimary_scalar_rearrange _ _ _ _ _ _ _ _ hm ha]
  have hpop : (Parameters.bodies n : ℝ)+2*Parameters.legs n=Parameters.dimension n := by
    exact_mod_cast Parameters.population_identity n
  rw [hpop]
  simp only [actualSafeBodyMean,actualFairSliceMean,Bool.false_eq_true,if_false,if_true,Int.cast_natCast]
  ring

theorem actual_activation_inverse_bound_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,|(actualActivationInverseApprox constant n n : ℝ)|≤2*(n : ℝ)^5 := by
  have hs := actualActivationInverseError_negligible.tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ)<1)
  filter_upwards [actual_activation_inverse_program_eventually constant hc,
    v7Activation_lower_eventually (constant : ℝ) (by exact_mod_cast hc),hs,eventually_ge_atTop 1]
    with n he hl hs hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
  have hrho : 0<v7Activation (constant : ℝ) n := lt_of_lt_of_le (by positivity : 0<((n : ℝ)^5)⁻¹) hl
  have hi : (v7Activation (constant : ℝ) n)⁻¹≤(n : ℝ)^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0<((n : ℝ)^5)⁻¹) hl
    simpa only [one_div,inv_inv] using hh
  have htri := abs_add_le ((actualActivationInverseApprox constant n n : ℝ)-
    (v7Activation (constant : ℝ) n)⁻¹) ((v7Activation (constant : ℝ) n)⁻¹)
  rw [sub_add_cancel] at htri
  rw [abs_of_pos (inv_pos.mpr hrho)] at htri
  have hp := one_le_pow₀ hn1 (n:=5)
  linarith

def actualBasePrimaryProgramError (n : ℕ) : ℝ :=
  10*(n : ℝ)^65*(actualActivationInverseError n+actualBodyBlurProgramError n+actualPairSourceProgramError n)

theorem actualBasePrimaryProgramError_negligible : Negligible actualBasePrimaryProgramError := by
  convert (((actualActivationInverseError_negligible.add actualBodyBlurProgramError_negligible).add
    actualPairSourceProgramError_negligible).mul_polynomial 65).const_mul 10 using 1
  funext n
  unfold actualBasePrimaryProgramError
  ring

theorem calibration_value_error (inverseApprox inverse dimensionTerm bodyCoefficient
    bodyApprox body shiftedApprox shifted unshiftedApprox unshifted : ℝ)
    (hb : |body|≤1) (hs : |shifted|≤1) :
    |(inverseApprox*(dimensionTerm-bodyCoefficient*bodyApprox-2*shiftedApprox)+
        2*unshiftedApprox-bodyApprox)-
      (inverse*(dimensionTerm-bodyCoefficient*body-2*shifted)+2*unshifted-body)|≤
      |inverseApprox-inverse| *(|dimensionTerm|+|bodyCoefficient|+2)+
      |inverseApprox| *(|bodyCoefficient| *|bodyApprox-body|+2*|shiftedApprox-shifted|)+
      2*|unshiftedApprox-unshifted|+|bodyApprox-body| := by
  have ha : |dimensionTerm-bodyCoefficient*body-2*shifted|≤|dimensionTerm|+|bodyCoefficient|+2 := by
    calc
      _ ≤ |dimensionTerm-bodyCoefficient*body|+|2*shifted| := abs_sub _ _
      _ ≤ (|dimensionTerm|+|bodyCoefficient*body|)+|2*shifted| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ _ := by rw [abs_mul,abs_mul]; norm_num; nlinarith [abs_nonneg bodyCoefficient]
  have hd : |(-bodyCoefficient)*(bodyApprox-body)-2*(shiftedApprox-shifted)|≤
      |bodyCoefficient| *|bodyApprox-body|+2*|shiftedApprox-shifted| := by
    simpa only [abs_mul,abs_neg,abs_of_pos (by norm_num : (0 : ℝ)<2)] using
      abs_sub ((-bodyCoefficient)*(bodyApprox-body)) (2*(shiftedApprox-shifted))
  rw [show (inverseApprox*(dimensionTerm-bodyCoefficient*bodyApprox-2*shiftedApprox)+
      2*unshiftedApprox-bodyApprox)-
      (inverse*(dimensionTerm-bodyCoefficient*body-2*shifted)+2*unshifted-body)=
      ((inverseApprox-inverse)*(dimensionTerm-bodyCoefficient*body-2*shifted)+
        inverseApprox*((-bodyCoefficient)*(bodyApprox-body)-2*(shiftedApprox-shifted)))+
        2*(unshiftedApprox-unshifted)-(bodyApprox-body) by ring]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl).trans
  simp only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  gcongr

/-- The actual base primary is approximated uniformly at every palette
color, with a fully instantiated negligible error and no numerical oracle. -/
theorem actual_base_primary_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ color : Fin (Parameters.modulus n),
      |(actualBasePrimaryProgram constant n color.val : ℝ)-
        basePrimary n (constant : ℝ) (boundaryHalf (constant : ℝ) n)
          (bodyShift (constant : ℝ) n) (bodyBlur (constant : ℝ) n)
          (startsPlus (constant : ℝ) n) (startsMinus (constant : ℝ) n)
          (pairSourceShift (constant : ℝ) n) (pairSourceLaw (constant : ℝ) n) color|≤
        actualBasePrimaryProgramError n := by
  filter_upwards [actual_body_mean_program_eventually constant,actual_fair_slice_program_eventually constant,
    actual_activation_inverse_program_eventually constant hc,actual_activation_inverse_bound_eventually constant hc,
    eventually_ge_atTop 2] with n hb hs hi hInv hn color
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hN : (Parameters.dimension n : ℝ)≤2*(n : ℝ)^60 := by
    have hh := (Parameters.dimension_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hB : (Parameters.bodies n : ℝ)≤2*(n : ℝ)^60 := by
    apply le_trans (b := (Parameters.dimension n : ℝ)) ?_ hN
    exact_mod_cast (show Parameters.bodies n≤Parameters.dimension n by unfold Parameters.bodies;omega)
  have hm1 : (1 : ℝ)≤Parameters.legs n := by
    have hh : 0<Parameters.legs n := by unfold Parameters.legs; have := Parameters.security_ge_two n; positivity
    exact_mod_cast hh
  have hq1 : (1 : ℝ)≤Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  let d : ℝ := (Parameters.dimension n : ℝ)/((Parameters.legs n : ℝ)*Parameters.modulus n)
  let c : ℝ := (Parameters.bodies n : ℝ)/Parameters.legs n
  have hd0 : 0≤d := by dsimp only [d]; positivity
  have hc0 : 0≤c := by dsimp only [c]; positivity
  have hd : d≤2*(n : ℝ)^60 := by
    apply le_trans (div_le_self (Nat.cast_nonneg _) ?_) hN
    nlinarith
  have hcc : c≤2*(n : ℝ)^60 := (div_le_self (Nat.cast_nonneg _) hm1).trans hB
  have he := calibration_value_error (actualActivationInverseApprox constant n n)
    ((v7Activation (constant : ℝ) n)⁻¹) d c
    (actualBodyMeanProgram constant n color.val) (actualSafeBodyMean (constant : ℝ) n color.val)
    (actualFairSliceProgram constant n true color.val) (actualFairSliceMean (constant : ℝ) n true color.val)
    (actualFairSliceProgram constant n false color.val) (actualFairSliceMean (constant : ℝ) n false color.val)
    (actualSafeBodyMean_abs_le_one _ _ _) (actualFairSliceMean_abs_le_one _ _ _ _)
  rw [actualBasePrimary_rearrange _ _ (by exact_mod_cast hc) (by omega)]
  simp only [actualBasePrimaryProgram,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_natCast,actualDimensionProgram_eq,actualLegPopulationProgram_eq,
    actualRootPopulationProgram_eq,ParameterProgram.modulus_value]
  change |(_ : ℝ)-_|≤_
  apply he.trans
  rw [abs_of_nonneg hd0,abs_of_nonneg hc0]
  have hb' := hb color.val
  have hs' := hs true color.val
  have hu' := hs false color.val
  change |(actualBodyMeanProgram constant n color.val : ℝ)-actualSafeBodyMean (constant : ℝ) n color.val|≤_ at hb'
  change |(actualFairSliceProgram constant n true color.val : ℝ)-actualFairSliceMean (constant : ℝ) n true color.val|≤_ at hs'
  change |(actualFairSliceProgram constant n false color.val : ℝ)-actualFairSliceMean (constant : ℝ) n false color.val|≤_ at hu'
  have hb0 : 0≤actualBodyBlurProgramError n := by
    unfold actualBodyBlurProgramError actualRootMarginalError;positivity
  have hs0 : 0≤actualPairSourceProgramError n := by
    unfold actualPairSourceProgramError;positivity
  have hi0 : 0≤actualActivationInverseError n := by unfold actualActivationInverseError;positivity
  have hp60 : (1 : ℝ)≤(n : ℝ)^60 := one_le_pow₀ hn1
  have hp65 : (1 : ℝ)≤(n : ℝ)^65 := one_le_pow₀ hn1
  have h560 : (n : ℝ)^5*(n : ℝ)^60=(n : ℝ)^65 := by rw [←pow_add]
  have h605 : (n : ℝ)^60≤(n : ℝ)^65 := pow_le_pow_right₀ hn1 (by decide)
  have h565 : (n : ℝ)^5≤(n : ℝ)^65 := pow_le_pow_right₀ hn1 (by decide)
  calc
    _ ≤ actualActivationInverseError n*(6*(n : ℝ)^60)+
        (2*(n : ℝ)^5)*((2*(n : ℝ)^60)*actualBodyBlurProgramError n+2*actualPairSourceProgramError n)+
        2*actualPairSourceProgramError n+actualBodyBlurProgramError n := by
      have hdc : d+c+2≤6*(n : ℝ)^60 := by linarith
      gcongr
    _ = (6*(n : ℝ)^60)*actualActivationInverseError n+
        (4*(n : ℝ)^65+1)*actualBodyBlurProgramError n+
        (4*(n : ℝ)^5+2)*actualPairSourceProgramError n := by
      rw [←h560]
      ring
    _ ≤ (10*(n : ℝ)^65)*actualActivationInverseError n+
        (10*(n : ℝ)^65)*actualBodyBlurProgramError n+
        (10*(n : ℝ)^65)*actualPairSourceProgramError n := by
      gcongr <;> linarith
    _ = actualBasePrimaryProgramError n := by unfold actualBasePrimaryProgramError;ring

end
end AFT.V7Calibration

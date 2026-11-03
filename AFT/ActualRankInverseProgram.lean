import AFT.ActualResponseProgram

/-! # An executable Sherman--Morrison preconditioner for the true response -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualRankDenominatorProgram (constant n : ℕ) : ℚ :=
  1+∑ color∈Finset.range (ParameterProgram.modulus n).value,
    paletteSignProgram (ParameterProgram.modulus n).value color*actualNormalizedSignProgram constant n color

def actualRankInverseProgram (constant n input output : ℕ) : ℚ :=
  (if input=output then 1 else 0)-
    (actualRankDenominatorProgram constant n)⁻¹*
      actualNormalizedSignProgram constant n output*paletteSignProgram (ParameterProgram.modulus n).value input

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance rankInverseProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualRankDenominator (constant : ℝ) (n : ℕ) : ℝ :=
  1+∑ color : Fin (Parameters.modulus n),paletteSign (Parameters.modulus n) color*actualNormalizedSign constant n color.val

def actualNormalizedRankInverse (constant : ℝ) (n : ℕ) :
    Module.End ℝ (Fin (Parameters.modulus n) → ℝ) :=
  primaryRankInverse 1 (fun color => actualNormalizedSign constant n color.val)
    (profileSignMap (paletteSign (Parameters.modulus n)))

theorem actualNormalizedSignProgramError_negligible : Negligible actualNormalizedSignProgramError := by
  have hh := (actualActivationInverseError_negligible.const_mul 2).add
    (((actualPairSourceProgramError_negligible.mul_polynomial 5).const_mul 4).add
      (actualPairSourceProgramError_negligible.const_mul 2))
  convert hh using 1
  funext n
  unfold actualNormalizedSignProgramError
  ring

theorem actual_normalized_sign_l1_eventually (constant : ℝ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      (∑ color : Fin (Parameters.modulus n),|actualNormalizedSign constant n color.val|)≤1/4 := by
  have hs := base_sign_estimates_eventually constant hc (boundaryHalf constant)
    (bodyShift constant) (bodyBlur constant) (startsPlus constant) (startsMinus constant)
    (pairSourceShift constant) (pairSourceLaw constant)
    ((actual_physical_supports_eventually constant hc).mono fun _ h => h.1)
  filter_upwards [hs,v7Activation_lower_eventually constant hc,eventually_ge_atTop 6] with n hs hl hn
  have hn2 : 2≤n := by omega
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hnorm (color : Fin (Parameters.modulus n)) := actualNormalizedSign_eq constant n hc (by omega) color
  have hrho : 0<v7Activation constant n := lt_of_lt_of_le (by positivity : 0<((n : ℝ)^5)⁻¹) hl
  have hinv : (v7Activation constant n)⁻¹≤(n : ℝ)^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0<((n : ℝ)^5)⁻¹) hl
    simpa only [one_div,inv_inv] using hh
  have hsign := hs.2.2.1
  have hratio := v7_anchor_ratio_bound n
  rw [Parameters.security_eq n hn2] at hratio
  have hl1 := hsign.trans (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ)≤32))
  simp_rw [hnorm,abs_mul,abs_of_pos (inv_pos.mpr hrho)]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (n : ℝ)^5*(32*(1/(n : ℝ)^8)) := by gcongr
    _ = 32/(n : ℝ)^3 := by field_simp
    _ ≤ 1/4 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ)<(n : ℝ)^3)).mpr
      have hpow : (6 : ℝ)^3≤(n : ℝ)^3 := by gcongr;exact_mod_cast hn
      norm_num at hpow
      linarith

theorem actualRankDenominator_bounds_eventually (constant : ℝ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      3/4≤actualRankDenominator constant n ∧ actualRankDenominator constant n≤5/4 := by
  filter_upwards [actual_normalized_sign_l1_eventually constant hc] with n hh
  have hs : |∑ color : Fin (Parameters.modulus n),paletteSign (Parameters.modulus n) color*
      actualNormalizedSign constant n color.val|≤1/4 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply le_trans (Finset.sum_le_sum (fun color _ => ?_)) hh
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (paletteSign_abs_le _ _)
  unfold actualRankDenominator
  constructor <;> linarith [abs_le.mp hs]

theorem actualRankDenominatorProgram_cast (constant n : ℕ) :
    (actualRankDenominatorProgram constant n : ℝ)=
      1+∑ color : Fin (Parameters.modulus n),paletteSign (Parameters.modulus n) color*
        (actualNormalizedSignProgram constant n color.val : ℝ) := by
  simp only [actualRankDenominatorProgram,Rat.cast_add,Rat.cast_one,Rat.cast_sum,Rat.cast_mul,
    ParameterProgram.modulus_value]
  rw [←Fin.sum_univ_eq_sum_range (fun color : ℕ =>
    (paletteSignProgram (Parameters.modulus n) color : ℝ)*(actualNormalizedSignProgram constant n color : ℝ))]
  congr 1
  apply Finset.sum_congr rfl
  intro color _
  rw [paletteSignProgram_cast]

def actualRankDenominatorProgramError (n : ℕ) : ℝ :=
  2*(n : ℝ)^40*actualNormalizedSignProgramError n

theorem actualRankDenominatorProgramError_negligible : Negligible actualRankDenominatorProgramError := by
  convert (actualNormalizedSignProgramError_negligible.mul_polynomial 40).const_mul 2 using 1
  funext n
  unfold actualRankDenominatorProgramError
  ring

theorem actual_rank_denominator_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      |(actualRankDenominatorProgram constant n : ℝ)-actualRankDenominator (constant : ℝ) n|≤
        actualRankDenominatorProgramError n := by
  filter_upwards [actual_normalized_sign_program_eventually constant hc,eventually_ge_atTop 2] with n hh hn
  rw [actualRankDenominatorProgram_cast,actualRankDenominator]
  rw [add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _color : Fin (Parameters.modulus n),actualNormalizedSignProgramError n := by
      apply Finset.sum_le_sum
      intro color _
      rw [←mul_sub,abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (paletteSign_abs_le _ _)).trans (hh color.val)
    _ ≤ actualRankDenominatorProgramError n := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hq := (Parameters.modulus_bounds n).2
      rw [Parameters.security_eq n hn] at hq
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq)
        (by unfold actualNormalizedSignProgramError actualActivationInverseError actualPairSourceProgramError
              actualBodyBlurProgramError actualRootMarginalError;positivity)

theorem actual_rank_denominator_program_positive_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,1/2≤(actualRankDenominatorProgram constant n : ℝ) := by
  have he := actualRankDenominatorProgramError_negligible.tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ)<1/4)
  filter_upwards [actual_rank_denominator_program_eventually constant hc,
    actualRankDenominator_bounds_eventually (constant : ℝ) (by exact_mod_cast hc),he] with n hh hb he
  have ht := (abs_le.mp hh).1
  linarith [hb.1]

theorem actualNormalizedRankInverse_basis (constant : ℝ) (n : ℕ)
    (input output : Fin (Parameters.modulus n)) :
    actualNormalizedRankInverse constant n (Pi.single input 1) output=
      (if input=output then 1 else 0)-(actualRankDenominator constant n)⁻¹*
        actualNormalizedSign constant n output.val*paletteSign (Parameters.modulus n) input := by
  unfold actualNormalizedRankInverse
  rw [primaryRankInverse_apply]
  have hsign : profileSignMap (paletteSign (Parameters.modulus n)) (Pi.single input 1)=
      paletteSign (Parameters.modulus n) input := by
    simp [profileSignMap,signFunctional,Pi.single_apply]
  rw [hsign]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply,eq_comm,
    actualRankDenominator,profileSignMap,LinearMap.coe_mk,AddHom.coe_mk,signFunctional]
  ring

theorem reciprocal_error_of_half_le (approximate actual error : ℝ)
    (ha : 1/2≤approximate) (hb : 1/2≤actual) (he : |approximate-actual|≤error) :
    |approximate⁻¹-actual⁻¹|≤4*error := by
  have ha0 : 0<approximate := by linarith
  have hb0 : 0<actual := by linarith
  have hia : approximate⁻¹≤2 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/2) ha
    norm_num [one_div] at hh
    exact hh
  have hib : actual⁻¹≤2 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/2) hb
    norm_num [one_div] at hh
    exact hh
  have he0 : 0≤error := (abs_nonneg _).trans he
  rw [show approximate⁻¹-actual⁻¹=(actual-approximate)*approximate⁻¹*actual⁻¹ by field_simp]
  rw [abs_mul,abs_mul,abs_of_pos (inv_pos.mpr ha0),abs_of_pos (inv_pos.mpr hb0),abs_sub_comm]
  calc
    _ ≤ error*2*2 := by gcongr
    _ = _ := by ring

def actualRankInverseProgramError (n : ℕ) : ℝ :=
  4*actualRankDenominatorProgramError n+2*actualNormalizedSignProgramError n

theorem actualRankInverseProgramError_negligible : Negligible actualRankInverseProgramError :=
  (actualRankDenominatorProgramError_negligible.const_mul 4).add
    (actualNormalizedSignProgramError_negligible.const_mul 2)

/-- Quantitative approximation of every entry of the exact rank-one
inverse; the actual denominator lower bound is proved above. -/
theorem actual_rank_inverse_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ input output : Fin (Parameters.modulus n),
      |(actualRankInverseProgram constant n input.val output.val : ℝ)-
        actualNormalizedRankInverse (constant : ℝ) n (Pi.single input 1) output|≤
        actualRankInverseProgramError n := by
  filter_upwards [actual_rank_denominator_program_positive_eventually constant hc,
    actualRankDenominator_bounds_eventually (constant : ℝ) (by exact_mod_cast hc),
    actual_rank_denominator_program_eventually constant hc,
    actual_normalized_sign_program_eventually constant hc,
    actual_normalized_sign_l1_eventually (constant : ℝ) (by exact_mod_cast hc)]
    with n hapos hpos hden hsign hl1 input output
  have hbpos : (1 : ℝ)/2≤actualRankDenominator (constant : ℝ) n := by linarith [hpos.1]
  have hinv := reciprocal_error_of_half_le _ _ _ hapos hbpos hden
  have hia : (actualRankDenominatorProgram constant n : ℝ)⁻¹≤2 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/2) hapos
    norm_num [one_div] at hh
    exact hh
  have hia0 : 0<(actualRankDenominatorProgram constant n : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hpoint : |actualNormalizedSign (constant : ℝ) n output.val|≤1 := by
    have hh' : |actualNormalizedSign (constant : ℝ) n output.val|≤
        ∑ color : Fin (Parameters.modulus n),|actualNormalizedSign (constant : ℝ) n color.val| :=
      Finset.single_le_sum (f:=fun color : Fin (Parameters.modulus n) =>
        |actualNormalizedSign (constant : ℝ) n color.val|) (fun color _ => abs_nonneg _) (Finset.mem_univ output)
    linarith [hh'.trans hl1]
  have he0 : 0≤actualNormalizedSignProgramError n := by
    unfold actualNormalizedSignProgramError actualActivationInverseError actualPairSourceProgramError
      actualBodyBlurProgramError actualRootMarginalError
    positivity
  have hd0 : 0≤actualRankDenominatorProgramError n := by unfold actualRankDenominatorProgramError;positivity
  rw [actualNormalizedRankInverse_basis]
  simp only [actualRankInverseProgram,Rat.cast_sub,Rat.cast_mul,Rat.cast_inv,
    ParameterProgram.modulus_value,paletteSignProgram_cast]
  have heq : ((if input.val=output.val then 1 else 0 : ℚ) : ℝ)=
      (if input=output then 1 else 0 : ℝ) := by simp only [Fin.val_inj];split_ifs <;> norm_num
  rw [heq]
  rw [show ∀ delta a b c d sign : ℝ,(delta-a*b*sign)-(delta-c*d*sign)=-(a*b-c*d)*sign by intros;ring]
  rw [abs_mul,abs_neg]
  apply (mul_le_of_le_one_right (abs_nonneg _) (paletteSign_abs_le _ _)).trans
  apply (approximation_mul_error _ _ _ _).trans
  rw [abs_of_pos hia0]
  calc
    _ ≤ (4*actualRankDenominatorProgramError n)*1+2*actualNormalizedSignProgramError n := by
      gcongr
      exact hsign output.val
    _ = _ := by unfold actualRankInverseProgramError;ring

theorem actual_normalized_rank_inverse_exact_eventually (constant : ℝ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      ∀ profile : Fin (Parameters.modulus n) → ℝ,
        actualNormalizedRankInverse constant n
          (primaryRankOperator 1 (fun color => actualNormalizedSign constant n color.val)
            (profileSignMap (paletteSign (Parameters.modulus n))) profile)=profile ∧
        primaryRankOperator 1 (fun color => actualNormalizedSign constant n color.val)
          (profileSignMap (paletteSign (Parameters.modulus n)))
          (actualNormalizedRankInverse constant n profile)=profile := by
  filter_upwards [actualRankDenominator_bounds_eventually constant hc] with n hh profile
  have hd : 1+profileSignMap (paletteSign (Parameters.modulus n))
      (fun color => actualNormalizedSign constant n color.val)≠0 := by
    change actualRankDenominator constant n≠0
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ)<3/4) hh.1)
  exact ⟨primaryRankInverse_left _ _ _ one_ne_zero hd profile,
    primaryRankInverse_right _ _ _ one_ne_zero hd profile⟩

theorem actual_normalized_rank_forward (constant : ℝ) (n : ℕ) (hc : 1≤constant) (hn : 1≤n) :
    primaryRankOperator 1 (fun color => actualNormalizedSign constant n color.val)
      (profileSignMap (paletteSign (Parameters.modulus n)))=
    primaryRankOperator (v7Activation constant n)
      (signResponse n constant (boundaryHalf constant n) (startsPlus constant n) (startsMinus constant n)
        (pairSourceShift constant n) (pairSourceLaw constant n))
      (profileSignMap (paletteSign (Parameters.modulus n))) := by
  apply LinearMap.ext
  intro profile
  funext output
  simp only [primaryRankOperator_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,inv_one,one_mul,
    actualNormalizedSign_eq constant n hc hn]
  ring

theorem actual_rank_preconditioner_exact_eventually (constant : ℝ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      let forward := primaryRankOperator (v7Activation constant n)
        (signResponse n constant (boundaryHalf constant n) (startsPlus constant n) (startsMinus constant n)
          (pairSourceShift constant n) (pairSourceLaw constant n))
        (profileSignMap (paletteSign (Parameters.modulus n)))
      ∀ profile,actualNormalizedRankInverse constant n (forward profile)=profile ∧
        forward (actualNormalizedRankInverse constant n profile)=profile := by
  filter_upwards [actual_normalized_rank_inverse_exact_eventually constant hc,eventually_ge_atTop 1] with n hh hn
  dsimp only
  rw [←actual_normalized_rank_forward constant n hc hn]
  exact hh

end
end AFT.V7Calibration

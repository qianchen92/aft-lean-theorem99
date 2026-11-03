import AFT.ActualAnchorProgram
import AFT.ActualPairedPublic

/-! # Executable compensated center probabilities for the paired score -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- Exactly the safe uniform core, evaluated with integer comparisons. -/
def actualCoreProgram (n color : ℕ) : ℚ :=
  if actualSafeMarginProgram n ≤ color ∧ color<(ParameterProgram.modulus n).value-actualSafeMarginProgram n
    then (actualSafeSizeProgram n : ℚ)⁻¹ else 0

def actualPublicAnchorMeanProgram (constant n : ℕ) (beta : ℚ) (center : ℕ) : ℚ :=
  ∑ color∈Finset.range (ParameterProgram.modulus n).value,
    actualPrimaryProgram constant n beta color*
      publicAnchorKernelProgram (ParameterProgram.modulus n).value (actualAnchorWidthProgram n) color center

def actualBodyCompensationProgram (constant n : ℕ) : ℚ :=
  (actualLegPopulationProgram n : ℚ)*actualActivationApprox constant n n/actualRootPopulationProgram n

/-- This is the actual compensated law P, rather than the blurred-core mean. -/
def actualBodyCenterProgram (constant n : ℕ) (beta : ℚ) (center : ℕ) : ℚ :=
  (1+actualBodyCompensationProgram constant n)*actualCoreProgram n center-
    actualBodyCompensationProgram constant n*actualPublicAnchorMeanProgram constant n beta center

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance bodyCenterProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

 theorem actualCoreProgram_cast (n : ℕ) (color : Fin (Parameters.modulus n)) :
    (actualCoreProgram n color.val : ℝ)=(actualCoreLaw n).weight color := by
  rw [actualCoreLaw_weight]
  have hm : color∈safePalette n ↔ actualSafeMarginProgram n ≤ color.val ∧
      color.val<(ParameterProgram.modulus n).value-actualSafeMarginProgram n := by
    simp only [safePalette,TrimmedSlice.paletteSlice,Finset.mem_filter,Finset.mem_univ,true_and,
      TrimmedSlice.mem_slice,actualSafeMarginProgram_eq,ParameterProgram.modulus_value]
    have hs := Parameters.safeSize_positive n
    unfold Parameters.safeSize at hs
    omega
  simp only [actualCoreProgram,uniformFiniteProfile,hm,safePalette_card,actualSafeSizeProgram_eq]
  split_ifs <;> simp only [Rat.cast_inv,Rat.cast_natCast,Rat.cast_zero]

 theorem actualPublicAnchorMeanProgram_error (constant n : ℕ) (beta : ℚ)
    (error : ℝ) (he : ∀ color : Fin (Parameters.modulus n),
      |(actualPrimaryProgram constant n beta color.val : ℝ)-actualPrimary (constant : ℝ) n beta color| ≤ error)
    (center : Fin (Parameters.modulus n)) :
    |(actualPublicAnchorMeanProgram constant n beta center.val : ℝ)-
      anchorMean (Parameters.modulus n) (Parameters.anchorWidth n) (actualPrimary (constant : ℝ) n beta) center.val| ≤ 
      (Parameters.modulus n : ℝ)*error := by
  have hsum : (actualPublicAnchorMeanProgram constant n beta center.val : ℝ)=
      ∑ color : Fin (Parameters.modulus n),(actualPrimaryProgram constant n beta color.val : ℝ)*
        publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val := by
    simp only [actualPublicAnchorMeanProgram,ParameterProgram.modulus_value,Rat.cast_sum,Rat.cast_mul,
      actualAnchorWidthProgram_eq]
    rw [←Fin.sum_univ_eq_sum_range]
    simp only [publicAnchorKernelProgram_cast]
  rw [hsum,anchorMean,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun color _ => show
      |(actualPrimaryProgram constant n beta color.val : ℝ)*publicAnchorKernel _ _ color center.val-
        actualPrimary (constant : ℝ) n beta color*publicAnchorKernel _ _ color center.val| ≤ error from by
    rw [←sub_mul,abs_mul]
    have hk : |publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val| ≤ 1 := by
      rw [←publicAnchorKernelProgram_cast]
      exact publicAnchorKernelProgram_abs_le_one _ _ _ _
    exact (mul_le_mul_of_nonneg_left hk (abs_nonneg _)).trans (by simpa only [mul_one] using he color))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

 theorem actualBodyCompensationProgram_error (constant n : ℕ) (hc : 1 ≤ constant) (hn : 1 ≤ n) :
    |(actualBodyCompensationProgram constant n : ℝ)-bodyCompensation n constant| ≤ 1/(2 : ℝ)^n := by
  have hratio : (Parameters.legs n : ℝ)/Parameters.bodies n ≤ 1 := (legs_fraction_small n).trans (by norm_num)
  have hr : 0 ≤ (Parameters.legs n : ℝ)/Parameters.bodies n := by positivity
  have ha := actualActivationApprox_error constant n n hc hn
  simp only [actualBodyCompensationProgram,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,
    actualLegPopulationProgram_eq,actualRootPopulationProgram_eq,bodyCompensation]
  rw [show ∀ a b c d : ℝ,a*b/d-a*c/d=(a/d)*(b-c) by intros;ring,abs_mul,abs_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_right hratio (abs_nonneg _)).trans (by simpa only [one_mul] using ha)

def actualBodyCenterProgramError (n : ℕ) : ℝ :=
  2/(2 : ℝ)^n+4*(n : ℝ)^40*actualPrimaryProgramError n

 theorem actualBodyCenterProgramError_negligible : Negligible actualBodyCenterProgramError := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n
    simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  convert (hm.const_mul 2).add ((actualPrimaryProgramError_negligible.mul_polynomial 40).const_mul 4) using 1
  funext n
  unfold actualBodyCenterProgramError
  ring

 theorem actual_body_center_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ color : Fin (Parameters.modulus n),
    |(actualBodyCenterProgram constant n (beta n) color.val : ℝ)-actualBodyCenter constant n (beta n) color| ≤ 
      actualBodyCenterProgramError n := by
  filter_upwards [actual_primary_program_eventually constant hc,
    actual_primary_probability_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    hbeta,eventually_ge_atTop 2] with n hp hprob hb hn color
  let delta : ℝ := bodyCompensation n constant
  let approximateDelta : ℝ := actualBodyCompensationProgram constant n
  let core : ℝ := (actualCoreLaw n).weight color
  let mean : ℝ := anchorMean (Parameters.modulus n) (Parameters.anchorWidth n)
    (actualPrimary constant n (beta n)) color.val
  let approximateMean : ℝ := actualPublicAnchorMeanProgram constant n (beta n) color.val
  have hdelta := actualBodyCompensationProgram_error constant n hc (by omega)
  have hmean := actualPublicAnchorMeanProgram_error constant n (beta n) _ (hp _ hb.1) color
  have hm0 : 0 ≤ mean := Finset.sum_nonneg (fun input _ => mul_nonneg (hprob.1 input).le (publicAnchorKernel_nonneg _ _ _ _))
  have hm1 : mean ≤ 1 := by
    calc
      _  ≤  ∑ input : Fin (Parameters.modulus n),actualPrimary constant n (beta n) input*1 := by
        apply Finset.sum_le_sum
        intro input _
        apply mul_le_mul_of_nonneg_left _ (hprob.1 input).le
        have hh := publicAnchorKernelProgram_abs_le_one (Parameters.modulus n) (Parameters.anchorWidth n) input.val color.val
        rw [publicAnchorKernelProgram_cast] at hh
        exact (le_abs_self _).trans hh
      _ = 1 := by simp only [mul_one,hprob.2]
  have hc0 : 0 ≤ core := (actualCoreLaw n).nonneg color
  have hc1 : core ≤ 1 := by
    simpa only [(actualCoreLaw n).sum_one] using Finset.single_le_sum
      (fun input (_ : input∈Finset.univ) => (actualCoreLaw n).nonneg input) (Finset.mem_univ color)
  have ha0 : 0 ≤ v7Activation constant n :=
    (activation_positive _ _ _ _ (legFeatureCount_positive (constant : ℝ) n (by exact_mod_cast hc) (by omega))).le
  have hd0 : 0 ≤ delta := by unfold delta bodyCompensation; positivity
  have hd1 : delta ≤ 1 := by
    have ha : v7Activation constant n ≤ 1 := (activation_le_one_hundredth _ _ _ _).trans (by norm_num)
    have hr := legs_fraction_small n
    unfold delta bodyCompensation
    calc
      _  ≤  (Parameters.legs n : ℝ)*1/Parameters.bodies n := by gcongr
      _  ≤  1 := by simpa only [mul_one] using hr.trans (by norm_num)
  have hmesh : 1/(2 : ℝ)^n ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hda : |approximateDelta| ≤ 2 := by
    have hh := (abs_sub_le_iff.mp hdelta).1
    have hh' := (abs_sub_le_iff.mp hdelta).2
    apply abs_le.mpr
    dsimp only [approximateDelta,delta] at *
    constructor <;> linarith
  have hdiff : |core-mean| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    simpa only [Parameters.security_eq n hn,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using
      (show (Parameters.modulus n : ℝ) ≤ 2*(Parameters.security n : ℝ)^40 by exact_mod_cast (Parameters.modulus_bounds n).2)
  have he : 0 ≤ actualPrimaryProgramError n := (abs_nonneg _).trans (hp (beta n) hb.1 color)
  simp only [actualBodyCenterProgram,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_one,actualCoreProgram_cast,
    actualBodyCenter,calibratedBodyProfile,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  change |(1+approximateDelta)*core-approximateDelta*approximateMean-((1+delta)*core-delta*mean)| ≤ _
  rw [show (1+approximateDelta)*core-approximateDelta*approximateMean-((1+delta)*core-delta*mean)=
    (approximateDelta-delta)*(core-mean)-approximateDelta*(approximateMean-mean) by ring]
  apply (abs_sub _ _).trans
  simp only [abs_mul]
  have hh := add_le_add (mul_le_mul hdelta hdiff (abs_nonneg _) (by positivity))
    (mul_le_mul hda hmean (abs_nonneg _) (by norm_num))
  apply hh.trans
  unfold actualBodyCenterProgramError
  have hx := mul_le_mul_of_nonneg_right hq he
  calc
    _ ≤ 1/(2 : ℝ)^n*2+2*(2*(n : ℝ)^40*actualPrimaryProgramError n) := by gcongr
    _ = _ := by ring

end
end AFT.V7Calibration

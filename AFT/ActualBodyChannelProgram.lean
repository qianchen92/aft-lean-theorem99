import AFT.ActualRootMarginalProgram
import AFT.ActualBodyCenterProgram
import AFT.ActualPairedMatrixProgram
import AFT.IndependentBodyPositive
import AFT.ActualResponseProgram

/-! # Executable independent root/body channels -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram Filter
open scoped BigOperators

def actualBodyChannelProgram (n input output : ℕ) : ℚ :=
  ∑ root : Window (3*n^2-1),actualRootMarginalProgram n root*
    if ((root : ℤ)+input)%(ParameterProgram.modulus n).value=(output : ℤ) then 1 else 0

def independentBodyPositiveProgram (constant n : ℕ) (beta : ℚ) (output : ℕ) : ℚ :=
  ∑ input∈Finset.range (ParameterProgram.modulus n).value,
    probabilityClamp (actualBodyCenterProgram constant n beta input)*
      probabilityClamp (actualBodyChannelProgram n input output)

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local instance] actualModulusNeZero
local instance bodyChannelProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem paletteEmbedding_mod (n : ℕ) (value : ℤ) :
    ((paletteEmbedding n value).val : ℤ)=value%(Parameters.modulus n : ℤ) := by
  change (((ZMod.finEquiv (Parameters.modulus n)).symm (value : ZMod (Parameters.modulus n))).val : ℤ)=_
  rw [finEquiv_symm_val,ZMod.val_intCast]

theorem actualBodyChannel_integer_sum (n : ℕ) (input output : Fin (Parameters.modulus n)) :
    actualBodyChannel n input output=
      ∑ root : Window (v7RootCutoff n),
        (rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n)
          (Parameters.bodies_positive n)).weight root*
        if ((root : ℤ)+input.val)%(Parameters.modulus n : ℤ)=(output.val : ℤ) then 1 else 0 := by
  unfold actualBodyChannel actualRootLaw
  rw [FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro root _
  have he : paletteEmbedding n (root : ℤ)=output-input ↔
      ((root : ℤ)+input.val)%(Parameters.modulus n : ℤ)=(output.val : ℤ) := by
    have hadd : paletteEmbedding n ((root : ℤ)+input.val)=paletteEmbedding n (root : ℤ)+input := by
      rw [map_add,paletteEmbedding_color]
    rw [eq_sub_iff_add_eq,←hadd,←paletteEmbedding_mod]
    constructor
    · intro h;rw [h]
    · intro h;apply Fin.ext;exact_mod_cast h
  simp only [he]
  split_ifs <;> simp

def actualBodyChannelProgramError (n : ℕ) : ℝ := 6*(n : ℝ)^2*actualRootMarginalError n

theorem actualBodyChannelProgramError_negligible : Negligible actualBodyChannelProgramError := by
  convert (actualRootMarginalError_negligible.mul_polynomial 2).const_mul 6 using 1
  funext n;unfold actualBodyChannelProgramError;ring

theorem actual_body_channel_program_eventually :
    ∀ᶠ n : ℕ in atTop,∀ input output : Fin (Parameters.modulus n),
      |(actualBodyChannelProgram n input.val output.val : ℝ)-actualBodyChannel n input output| ≤
        actualBodyChannelProgramError n := by
  filter_upwards [actual_root_marginal_program_eventually,eventually_ge_atTop 2] with n hr hn input output
  have he : 0 ≤ actualRootMarginalError n := by unfold actualRootMarginalError;positivity
  have hcard : (Fintype.card (Window (v7RootCutoff n)) : ℝ) ≤ 6*(n : ℝ)^2 := by
    rw [←Fintype.card_congr (windowIndexEquiv _),Fintype.card_fin]
    unfold v7RootCutoff
    have hh : 2*(3*n^2-1)+1 ≤ 6*n^2 := by
      have h2 : 4 ≤ n^2 := by nlinarith
      omega
    exact_mod_cast hh
  simp only [actualBodyChannelProgram,Rat.cast_sum,Rat.cast_mul,ParameterProgram.modulus_value]
  rw [actualBodyChannel_integer_sum]
  simp only [v7RootCutoff]
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _root : Window (v7RootCutoff n),actualRootMarginalError n := by
      apply Finset.sum_le_sum
      intro root _
      split_ifs
      · simpa only [Rat.cast_one,mul_one] using hr root
      · simpa only [Rat.cast_zero,mul_zero,sub_self,abs_zero] using he
    _ = (Fintype.card (Window (v7RootCutoff n)) : ℝ)*actualRootMarginalError n := by simp
    _ ≤ actualBodyChannelProgramError n := mul_le_mul_of_nonneg_right hcard he

theorem actualBodyChannel_le_one (n : ℕ) (input output : Fin (Parameters.modulus n)) :
    actualBodyChannel n input output ≤ 1 := by
  simpa only [actualBodyChannel_mass] using Finset.single_le_sum
    (fun color (_ : color∈Finset.univ) => actualBodyChannel_nonneg n input color) (Finset.mem_univ output)

def independentBodyPositiveProgramError (n : ℕ) : ℝ :=
  2*(n : ℝ)^40*(actualBodyCenterProgramError n+actualBodyChannelProgramError n)

theorem independentBodyPositiveProgramError_negligible : Negligible independentBodyPositiveProgramError := by
  convert ((actualBodyCenterProgramError_negligible.add actualBodyChannelProgramError_negligible).mul_polynomial 40).const_mul 2 using 1
  funext n;unfold independentBodyPositiveProgramError;ring

theorem independent_body_positive_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ output : Fin (Parameters.modulus n),
      |(independentBodyPositiveProgram constant n (beta n) output.val : ℝ)-
        independentBodyPositiveProfile constant n (beta n) output| ≤ independentBodyPositiveProgramError n := by
  filter_upwards [actual_body_channel_program_eventually,actual_body_center_program_eventually constant hc beta hbeta,
    actual_reference_laws_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    eventually_ge_atTop 2] with n hchannel hcenter hlaws hn output
  have hp0 (input : Fin (Parameters.modulus n)) := (actualBodyLaw constant n (beta n)).nonneg input
  have hp1 (input : Fin (Parameters.modulus n)) : (actualBodyLaw constant n (beta n)).weight input ≤ 1 := by
    simpa only [(actualBodyLaw constant n (beta n)).sum_one] using Finset.single_le_sum
      (fun color (_ : color∈Finset.univ) => (actualBodyLaw constant n (beta n)).nonneg color) (Finset.mem_univ input)
  have hp (input : Fin (Parameters.modulus n)) : |(probabilityClamp (actualBodyCenterProgram constant n (beta n) input.val) : ℝ)-
      (actualBodyLaw constant n (beta n)).weight input| ≤ actualBodyCenterProgramError n := by
    apply (probabilityClamp_error _ _ (hp0 input) (hp1 input)).trans
    simpa only [hlaws.2.1] using hcenter input
  have hq (input : Fin (Parameters.modulus n)) := (probabilityClamp_error (actualBodyChannelProgram n input.val output.val)
    (actualBodyChannel n input output) (actualBodyChannel_nonneg ..) (actualBodyChannel_le_one ..)).trans (hchannel input output)
  have herror0 : 0 ≤ actualBodyCenterProgramError n+actualBodyChannelProgramError n := by
    exact add_nonneg ((abs_nonneg _).trans (hp output)) ((abs_nonneg _).trans (hchannel output output))
  have hmod : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    have hh := (Parameters.modulus_bounds n).2
    rw [Parameters.security_eq n hn] at hh
    exact_mod_cast hh
  have hprog : (independentBodyPositiveProgram constant n (beta n) output.val : ℝ)=
      ∑ input : Fin (Parameters.modulus n),(probabilityClamp (actualBodyCenterProgram constant n (beta n) input.val) : ℝ)*
        (probabilityClamp (actualBodyChannelProgram n input.val output.val) : ℝ) := by
    simp only [independentBodyPositiveProgram,Rat.cast_sum,Rat.cast_mul,ParameterProgram.modulus_value]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [hprog,independentBodyPositiveProfile,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _input : Fin (Parameters.modulus n),(actualBodyCenterProgramError n+actualBodyChannelProgramError n) := by
      apply Finset.sum_le_sum
      intro input _
      have hm := approximation_mul_error
        (probabilityClamp (actualBodyCenterProgram constant n (beta n) input.val) : ℝ)
        (probabilityClamp (actualBodyChannelProgram n input.val output.val) : ℝ)
        ((actualBodyLaw constant n (beta n)).weight input) (actualBodyChannel n input output)
      apply hm.trans
      have hb := probabilityClamp_bounds (actualBodyCenterProgram constant n (beta n) input.val)
      have htrue := actualBodyChannel_nonneg n input output
      rw [abs_of_nonneg hb.1,abs_of_nonneg htrue]
      exact add_le_add
        ((mul_le_mul (hp input) (actualBodyChannel_le_one ..) htrue ((abs_nonneg _).trans (hp input))).trans_eq (mul_one _))
        ((mul_le_mul hb.2 (hq input) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _))
    _ = (Parameters.modulus n : ℝ)*(actualBodyCenterProgramError n+actualBodyChannelProgramError n) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ ≤ independentBodyPositiveProgramError n := mul_le_mul_of_nonneg_right hmod herror0

end
end AFT.V7Calibration

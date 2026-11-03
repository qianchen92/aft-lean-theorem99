import AFT.ActualRankInverseProgram
import AFT.MatrixPrimaryActivity

/-! # Concrete contraction bounds for numerical response inversion -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance preconditionBoundsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def analysisBeta (n : ℕ) : ℝ := (Parameters.legs n : ℝ)/Parameters.dimension n

def analysisPrimary (constant : ℝ) (n : ℕ) : Fin (Parameters.modulus n) → ℝ :=
  GaussianSource.actualPrimary constant (analysisBeta n) n

def analysisRate (n : ℕ) : ℝ := 1/Real.sqrt (Parameters.legs n : ℝ)

def actualAnchorError (constant : ℝ) (n : ℕ) : Module.End ℝ (Fin (Parameters.modulus n) → ℝ) :=
  anchorError n (fun sample => bodyShift constant n sample.1)
    (compensatorRootShift constant n) (pairSourceLaw constant n)

theorem analysisBeta_typical (n : ℕ) :
    (Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤analysisBeta n ∧
      analysisBeta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n := by
  have hd : 0<(Parameters.dimension n : ℝ) := by
    have hh := Parameters.population_identity n
    have hb := Parameters.bodies_positive n
    exact_mod_cast (show 0<Parameters.dimension n by omega)
  unfold analysisBeta
  constructor <;> apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr <;> nlinarith

theorem analysisPrimary_estimates_eventually (constant : ℝ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,
      (∀ color,1/(4*(Parameters.modulus n : ℝ))≤analysisPrimary constant n color) ∧
      (∑ color,analysisPrimary constant n color)=1 ∧
      (∀ color,|actualNormalizedSign constant n color.val|≤2*analysisPrimary constant n color) := by
  have he := primary_estimates_eventually constant hc analysisBeta (boundaryHalf constant)
    (bodyShift constant) (bodyBlur constant) (startsPlus constant) (startsMinus constant)
    (pairSourceShift constant) (pairSourceLaw constant) (by
      filter_upwards [actual_physical_supports_eventually constant hc] with n h
      exact ⟨h.1,h.2,(analysisBeta_typical n).1,(analysisBeta_typical n).2⟩)
  filter_upwards [he,eventually_ge_atTop 1] with n he hn
  refine ⟨he.1,he.2.2.2.2,?_⟩
  intro color
  have hrho : 0<v7Activation constant n := activation_positive _ _ _ _ (legFeatureCount_positive constant n hc hn)
  rw [actualNormalizedSign_eq constant n hc hn,abs_mul,abs_of_pos (inv_pos.mpr hrho)]
  have hh := mul_le_mul_of_nonneg_left (he.2.1 color) (inv_nonneg.mpr hrho.le)
  calc
    _ ≤ _ := hh
    _ = 2*analysisPrimary constant n color := by unfold analysisPrimary GaussianSource.actualPrimary;field_simp

theorem analysisRate_bounds_eventually : ∀ᶠ n : ℕ in atTop,0<analysisRate n ∧ analysisRate n≤1/2 := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlegs : (4 : ℝ)≤Parameters.legs n := by
    simp only [Parameters.legs,Parameters.security_eq n hn,Nat.cast_pow]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) (show (2 : ℝ)≤n by exact_mod_cast hn) 30
    norm_num at h
    linarith
  have hs : 2≤Real.sqrt (Parameters.legs n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    norm_num only [show (2 : ℝ)^2=4 by norm_num]
    exact hlegs
  unfold analysisRate
  exact ⟨by positivity,(div_le_iff₀ (by positivity)).mpr (by linarith)⟩

theorem actual_rank_activity_bound_eventually (constant : ℝ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ profile,
      primaryActivity (analysisRate n) (analysisPrimary constant n) (actualNormalizedRankInverse constant n profile)≤
        4*primaryActivity (analysisRate n) (analysisPrimary constant n) profile := by
  filter_upwards [analysisPrimary_estimates_eventually constant hc,
    actual_normalized_sign_l1_eventually constant hc,actualRankDenominator_bounds_eventually constant hc,
    analysisRate_bounds_eventually] with n hp hl hd hr profile
  have hq : 0<(Parameters.modulus n : ℝ) := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hp' : ∀color,0<analysisPrimary constant n color := fun color => lt_of_lt_of_le (by positivity) (hp.1 color)
  have hsmall : (∑ color : Fin (Parameters.modulus n),|actualNormalizedSign constant n color.val|)<1 := by linarith
  have hh := finitePrimaryRankEquiv_activity_le (analysisRate n) 1 2
    (analysisPrimary constant n) (fun color : Fin (Parameters.modulus n) => actualNormalizedSign constant n color.val)
    (paletteSign (Parameters.modulus n)) profile hr.1.le hp' hp.2.1 (by norm_num)
    (paletteSign_abs_le _) hp.2.2 hsmall
  have heq : (finitePrimaryRankEquiv 1 (fun color : Fin (Parameters.modulus n) => actualNormalizedSign constant n color.val)
      (paletteSign (Parameters.modulus n)) (paletteSign_abs_le _) hsmall).symm profile=
      actualNormalizedRankInverse constant n profile := rfl
  rw [heq] at hh
  have hd' : 1+signFunctional (paletteSign (Parameters.modulus n))
      (fun color : Fin (Parameters.modulus n) => actualNormalizedSign constant n color.val)=actualRankDenominator constant n := rfl
  have hsqrt : Real.sqrt (2*(∑ color : Fin (Parameters.modulus n),|actualNormalizedSign constant n color.val|)/
      (actualRankDenominator constant n)^2)≤1 := by
    apply (Real.sqrt_le_one).mpr
    apply (div_le_iff₀ (by nlinarith [sq_nonneg (actualRankDenominator constant n)] : 0<(actualRankDenominator constant n)^2)).mpr
    nlinarith [sq_nonneg (actualRankDenominator constant n-3/4)]
  have hf : 2/|actualRankDenominator constant n|≤8/3 := by
    rw [abs_of_pos (by linarith : 0<actualRankDenominator constant n)]
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hconst : rankInverseActivityConstant (analysisRate n) 1 2
      (fun color : Fin (Parameters.modulus n) => actualNormalizedSign constant n color.val) (paletteSign (Parameters.modulus n))≤4 := by
    unfold rankInverseActivityConstant
    rw [hd']
    have hmul := mul_le_mul hr.2 hf (by positivity : 0≤2/|actualRankDenominator constant n|) (by norm_num : (0 : ℝ)≤1/2)
    linarith
  exact hh.trans (mul_le_mul_of_nonneg_right hconst (primaryActivity_nonneg _ _ _ hr.1.le))

theorem actual_anchor_activity_bound_eventually (constant : ℝ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ profile,
      primaryActivity (analysisRate n) (analysisPrimary constant n) (actualAnchorError constant n profile)≤
        (1/16)*primaryActivity (analysisRate n) (analysisPrimary constant n) profile := by
  have hsmall := (primaryTranslationEnvelope_tendsto 6 (1/4)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1/16))
  filter_upwards [hsmall,analysisPrimary_estimates_eventually constant hc,
    actual_shift_bound_eventually constant hc,analysisRate_bounds_eventually] with n hs hp hshift hr profile
  have hx : 0<(Parameters.security n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0<2) (Parameters.security_ge_two n)
  have hq : 0<(Parameters.modulus n : ℝ) := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hrate := v7_primary_pool_rate_bound n (Parameters.legs n) (by omega)
  have herr := intervalTranslationActivity_le_envelope (Parameters.security n) (Parameters.modulus n)
    (analysisRate n) 6 (1/4) (Parameters.anchorWidth n) hx hq
    (by exact_mod_cast (Parameters.modulus_bounds n).2) (by simp [Parameters.anchorWidth])
    hrate.2 (by norm_num) (by norm_num)
  have hinj : Function.Injective (fun color : Fin (Parameters.modulus n) => (color.val : ℤ)) := by
    intro a b hab
    apply Fin.ext
    dsimp only at hab
    exact_mod_cast hab
  have hb := averagedIntervalTranslationOperator_activity_le
    (fun color : Fin (Parameters.modulus n) => (color.val : ℤ))
    (errorStarts n (compensatorRootShift constant n))
    (errorShift (fun sample => bodyShift constant n sample.1) (compensatorRootShift constant n))
    (Parameters.anchorWidth n) (errorLaw (pairSourceLaw constant n)).weight hinj
    (analysisRate n) (6*(Parameters.security n : ℝ)^2) ((1/4 : ℝ)/Parameters.modulus n)
    (analysisPrimary constant n) profile (errorLaw _).nonneg (errorLaw _).sum_one hr.1.le
    (fun color => lt_of_lt_of_le (by positivity) (hp.1 color)) hp.2.1 (by positivity)
    (fun color => by convert hp.1 color using 1; ring) (fun sample => hshift sample.1)
  exact hb.trans (mul_le_mul_of_nonneg_right (herr.trans hs.le) (primaryActivity_nonneg _ _ _ hr.1.le))

theorem actual_preconditioned_contraction_eventually (constant : ℝ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ profile,
      primaryActivity (analysisRate n) (analysisPrimary constant n)
        (actualNormalizedRankInverse constant n (actualAnchorError constant n profile))≤
        (1/4)*primaryActivity (analysisRate n) (analysisPrimary constant n) profile := by
  filter_upwards [actual_rank_activity_bound_eventually constant hc,actual_anchor_activity_bound_eventually constant hc] with n hr he profile
  exact (hr _).trans ((mul_le_mul_of_nonneg_left (he profile) (by norm_num : (0 : ℝ)≤4)).trans_eq (by ring))

end
end AFT.V7Calibration

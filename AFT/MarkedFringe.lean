import AFT.MarkedParameters

/-! # The actual all-primary fringe of the marked endpoint pair -/

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

def primaryReferenceDifferenceDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (color : Fin (Parameters.modulus parameter)) : ℝ :=
  (actualPrimary cutoffScale parameter beta color-actualReferenceMean cutoffScale parameter beta color) /
    actualPrimary cutoffScale parameter beta color

def rootMeanDifferenceDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (color : Fin (Parameters.modulus parameter)) : ℝ :=
  (actualRootBodyMean parameter color-actualReferenceMean cutoffScale parameter beta color) /
    actualPrimary cutoffScale parameter beta color

def actualMarkedFringeInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) : InputSeed (Fin (Parameters.modulus parameter)) :=
  primaryPairInput (fun first second => primaryReferenceDifferenceDensity cutoffScale parameter beta first *
    rootMeanDifferenceDensity cutoffScale parameter beta second)

def markedFringeAggregateConstant : ℝ :=
  1152*(Real.sqrt (2*bodyMeanSquareConstant)+4*bodyMeanRelativeConstant)

theorem actual_root_body_mean_mass (parameter : ℕ) (hp : 2 ≤ parameter) :
    (∑ color, actualRootBodyMean parameter color) = 1 := by
  have hmargin : v7RootCutoff parameter ≤ Parameters.safeMargin parameter := by
    simp only [v7RootCutoff, Parameters.safeMargin, Parameters.security_eq parameter hp]
    omega
  have hh := rootProfileOperator_mass_of_support parameter (actualCoreLaw parameter).weight (by
    intro color hc
    have hin : color ∈ safePalette parameter := by
      by_contra hn
      simp only [actualCoreLaw, FiniteDist.uniformSafe, if_neg hn, ne_eq, not_true_eq_false] at hc
    simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
      TrimmedSlice.mem_slice] at hin
    omega)
  rw [rootProfileOperator_core, FiniteDist.sum_one] at hh
  exact hh

theorem actual_marked_fringe_factors_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      let p := actualPrimary cutoffScale parameter (beta parameter)
      let f := primaryReferenceDifferenceDensity cutoffScale parameter (beta parameter)
      let g := rootMeanDifferenceDensity cutoffScale parameter (beta parameter)
      (∀ color, |f color| ≤ 9) ∧ (∑ color, p color*f color^2) ≤ 81 ∧
      (∀ color, |g color| ≤ 2*bodyMeanRelativeConstant/(parameter : ℝ)^34) ∧
      (∑ color, p color*g color^2) ≤ 2*bodyMeanSquareConstant/(parameter : ℝ)^72 := by
  filter_upwards [actual_reference_primary_density_eventually cutoffScale hscale beta hbeta,
    actual_root_body_mean_bounds cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter href hroot hp hlarge
  dsimp only
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hRel : 0 ≤ bodyMeanRelativeConstant := by unfold bodyMeanRelativeConstant; positivity
  have hSquare : 0 ≤ bodyMeanSquareConstant := by unfold bodyMeanSquareConstant; positivity
  have hf (color) : |primaryReferenceDifferenceDensity cutoffScale parameter (beta parameter) color| ≤ 9 := by
    have heq : primaryReferenceDifferenceDensity cutoffScale parameter (beta parameter) color =
        1-actualReferenceMean cutoffScale parameter (beta parameter) color/actualPrimary cutoffScale parameter (beta parameter) color := by
      unfold primaryReferenceDifferenceDensity
      field_simp [ne_of_gt (hp.1 color)]
    rw [heq]
    have hh := abs_sub_le (1 : ℝ) 0 (actualReferenceMean cutoffScale parameter (beta parameter) color/actualPrimary cutoffScale parameter (beta parameter) color)
    simp only [sub_zero,zero_sub,abs_neg,abs_one] at hh
    linarith [(href.1 color)]
  refine ⟨hf, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∑ color, actualPrimary cutoffScale parameter (beta parameter) color*81 := by
        apply Finset.sum_le_sum
        intro color _
        apply mul_le_mul_of_nonneg_left _ (hp.1 color).le
        have hh := pow_le_pow_left₀ (abs_nonneg _) (hf color) 2
        norm_num only [sq_abs,show (9 : ℝ)^2=81 by norm_num] at hh
        exact hh
      _ = _ := by rw [← Finset.sum_mul,hp.2,one_mul]
  · intro color
    unfold rootMeanDifferenceDensity
    rw [abs_div, abs_of_pos (hp.1 color)]
    apply (div_le_iff₀ (hp.1 color)).mpr
    apply (hroot.1 color).trans
    apply mul_le_mul_of_nonneg_right _ (hp.1 color).le
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (34 : ℕ) ≤ (137/4 : ℝ))
  · have heq : (∑ color, actualPrimary cutoffScale parameter (beta parameter) color *
        rootMeanDifferenceDensity cutoffScale parameter (beta parameter) color^2) =
        profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter))
          (actualRootBodyMean parameter-actualReferenceMean cutoffScale parameter (beta parameter)) := by
      unfold profileSquareNorm
      apply Finset.sum_congr rfl
      intro color _
      unfold rootMeanDifferenceDensity
      simp only [Pi.sub_apply]
      field_simp
    rw [heq]
    apply hroot.2.trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (72 : ℕ) ≤ (289/4 : ℝ))

/-- This actual fringe remains canonical in both primary coordinates. -/
theorem actual_marked_fringe_canonical_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ primary : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      Hoeffding.Canonical (fun _ : Fin 2 => primary) Finset.univ
        (actualMarkedFringeInput cutoffScale parameter (beta parameter)).kernel := by
  filter_upwards [actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hp hr hlarge primary hprimary
  apply MixedKernel.pair_product_canonical
  · rw [hprimary]
    have heq : (∑ color, actualPrimary cutoffScale parameter (beta parameter) color *
        primaryReferenceDifferenceDensity cutoffScale parameter (beta parameter) color) =
        ∑ color, (actualPrimary cutoffScale parameter (beta parameter) color-actualReferenceMean cutoffScale parameter (beta parameter) color) := by
      apply Finset.sum_congr rfl
      intro color _
      unfold primaryReferenceDifferenceDensity
      field_simp [ne_of_gt (hp.1 color)]
    rw [heq,Finset.sum_sub_distrib,hp.2,hr.2,sub_self]
  · rw [hprimary]
    have heq : (∑ color, actualPrimary cutoffScale parameter (beta parameter) color *
        rootMeanDifferenceDensity cutoffScale parameter (beta parameter) color) =
        ∑ color, (actualRootBodyMean parameter color-actualReferenceMean cutoffScale parameter (beta parameter) color) := by
      apply Finset.sum_congr rfl
      intro color _
      unfold rootMeanDifferenceDensity
      field_simp [ne_of_gt (hp.1 color)]
    rw [heq,Finset.sum_sub_distrib,actual_root_body_mean_mass parameter hlarge,hr.2,sub_self]

/-- The all-primary part of the actual marked law is estimated after its
unconditional activation probability has canceled one inverse factor. -/
theorem actual_marked_fringe_total_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool : ℕ, Parameters.legs parameter ≤ 2*primaryPool →
      ∀ bodyPool radius : ℝ,
      (Parameters.legs parameter : ℝ)*v7Activation cutoffScale parameter *
        responseInputWeight primary body primaryPool bodyPool radius
          (4/v7Activation cutoffScale parameter) (actualMarkedFringeInput cutoffScale parameter (beta parameter)) ≤
            markedFringeAggregateConstant/(parameter : ℝ)^31 := by
  filter_upwards [actual_marked_fringe_factors_eventually cutoffScale hscale beta hbeta,
    v7Activation_lower_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hf hrho hp primary body hprimary pool hpool bodyPool radius
  let a := (Real.sqrt (pool : ℝ))⁻¹
  let K := Real.sqrt (2*bodyMeanSquareConstant)
  let R := bodyMeanRelativeConstant
  let rho := v7Activation cutoffScale parameter
  have ha := covariance_pool_rate parameter pool hp hpool
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hx0 : (0 : ℝ) < parameter := by positivity
  have hRel : 0 ≤ R := by unfold R bodyMeanRelativeConstant; positivity
  have hSquare : 0 ≤ bodyMeanSquareConstant := by unfold bodyMeanSquareConstant; positivity
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hsq : (K/(parameter : ℝ)^36)^2 = 2*bodyMeanSquareConstant/(parameter : ℝ)^72 := by
    dsimp only [K]
    rw [div_pow,Real.sq_sqrt (by positivity)]
    ring
  have hpair := MixedKernel.pair_product_activity_le primary primary
    (primaryReferenceDifferenceDensity cutoffScale parameter (beta parameter))
    (rootMeanDifferenceDensity cutoffScale parameter (beta parameter)) a a 9 9
    (K/(parameter : ℝ)^36) (2*R/(parameter : ℝ)^34)
    ha.1 ha.1 (by norm_num) (by norm_num) (by positivity) (by positivity)
    (by rw [hprimary]; norm_num only [show (9 : ℝ)^2=81 by norm_num]; exact hf.2.1)
    hf.1 (by rw [hprimary,hsq]; exact hf.2.2.2) hf.2.2.1
  have ha2 : a*a ≤ 4/(parameter : ℝ)^30 := by
    have hh := pow_le_pow_left₀ ha.1 ha.2.2 2
    convert hh using 1 <;> ring
  have ha9 : 9+a*9 ≤ 18 := by linarith [ha.2.1]
  have hY : a*(2*R/(parameter : ℝ)^34) ≤ 4*R/(parameter : ℝ)^36 := by
    calc
      _ ≤ (2/(parameter : ℝ)^15)*(2*R/(parameter : ℝ)^34) := mul_le_mul_of_nonneg_right ha.2.2 (by positivity)
      _ = 4*R/(parameter : ℝ)^49 := by field_simp; ring
      _ ≤ _ := by
        have hh := inverse_power_antitone hx (show 36 ≤ 49 by decide)
        convert mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*R by positivity) using 1 <;> ring
  have hinput : inputWeight primary body pool bodyPool radius (actualMarkedFringeInput cutoffScale parameter (beta parameter)) ≤
      72*(K+4*R)/(parameter : ℝ)^66 := by
    rw [actualMarkedFringeInput,primaryPairInput_weight]
    apply hpair.trans
    calc
      _ ≤ (4/(parameter : ℝ)^30)*18*(K/(parameter : ℝ)^36+4*R/(parameter : ℝ)^36) := by
        exact mul_le_mul (mul_le_mul ha2 ha9 (by positivity) (by positivity)) (add_le_add le_rfl hY)
          (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  have hrho0 : 0 < rho := lt_of_lt_of_le (by positivity : 0 < ((parameter : ℝ)^5)⁻¹) hrho
  have hinv : rho⁻¹ ≤ (parameter : ℝ)^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < ((parameter : ℝ)^5)⁻¹) hrho
    simpa only [one_div,inv_inv] using hh
  have hm : (Parameters.legs parameter : ℝ) = (parameter : ℝ)^30 := by
    simp only [Parameters.legs,Parameters.security_eq parameter hp,Nat.cast_pow]
  change (Parameters.legs parameter : ℝ)*rho*((4/rho)^2*inputWeight primary body pool bodyPool radius _) ≤ _
  calc
    _ = 16*(Parameters.legs parameter : ℝ)*rho⁻¹*inputWeight primary body pool bodyPool radius _ := by field_simp; ring
    _ ≤ 16*(parameter : ℝ)^30*(parameter : ℝ)^5*(72*(K+4*R)/(parameter : ℝ)^66) := by
      rw [hm]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hinv (by positivity)) hinput
        (by
          rw [actualMarkedFringeInput,primaryPairInput_weight]
          apply MixedKernel.activity_nonneg
          intro i
          fin_cases i <;> change 0 ≤ (Real.sqrt (pool : ℝ))⁻¹ <;> positivity) (by positivity)
    _ = _ := by unfold markedFringeAggregateConstant; dsimp only [K,R]; field_simp; ring

end
end AFT.V7Calibration

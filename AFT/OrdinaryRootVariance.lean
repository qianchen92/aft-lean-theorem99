import AFT.BodyTranslation
import AFT.V7ReferenceLaws

/-! # Exact root-shift variance of the actual uniform safe core -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {Source : Type*} [Fintype Source]

theorem scaled_indicator_variance (law : FiniteDist Source) (value : Source → ℝ)
    (scale : ℝ) (hvalue : ∀ source, value source ^ 2 = scale * value source) :
    (∑ source, law.weight source * (value source - ∑ other, law.weight other * value other)^2) =
      (∑ source, law.weight source * value source) *
        (scale - ∑ source, law.weight source * value source) := by
  let mean := ∑ source, law.weight source * value source
  have hp (source) : law.weight source * (value source-mean)^2 =
      scale*(law.weight source*value source)-2*mean*(law.weight source*value source)+
        mean^2*law.weight source := by
    have hh := congrArg (fun x : ℝ => law.weight source*x) (hvalue source)
    nlinarith
  change (∑ source, law.weight source*(value source-mean)^2) = mean*(scale-mean)
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, law.sum_one]
  change scale*mean-2*mean*mean+mean^2*1 = _
  ring

end
end AFT.FiniteDist

namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section

/-- The core variance uses the actual conditioned root marginal. -/
def rootCoreVariance (n : ℕ) (color : Fin (Parameters.modulus n)) : ℝ :=
  ∑ root : Window (v7RootCutoff n),
    (rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n)
      (Parameters.bodies_positive n)).weight root *
      (integerShiftProfile n (actualCoreLaw n).weight root color-actualRootBodyMean n color)^2

theorem integerShiftCore_eq (n : ℕ) (shift : ℤ) (color : Fin (Parameters.modulus n)) :
    integerShiftProfile n (actualCoreLaw n).weight shift color =
      coreIntegerProfile n ((color.val : ℤ)-shift) := by
  have he : (actualCoreLaw n).weight = fun center => coreIntegerProfile n center.val :=
    funext fun center => (coreIntegerProfile_on_palette n center).symm
  rw [he, integerShiftProfile_function n _ (coreIntegerProfile_support n)]

theorem rootCoreVariance_identity (n : ℕ) (color : Fin (Parameters.modulus n)) :
    rootCoreVariance n color = actualRootBodyMean n color *
      (1/(Parameters.safeSize n : ℝ)-actualRootBodyMean n color) := by
  have hh := FiniteDist.scaled_indicator_variance
    (rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n) (Parameters.bodies_positive n))
    (fun root : Window (v7RootCutoff n) => integerShiftProfile n (actualCoreLaw n).weight root color)
    (1/(Parameters.safeSize n : ℝ)) (by
      intro root
      dsimp only
      rw [integerShiftCore_eq]
      unfold coreIntegerProfile intervalAnchorLaw
      split_ifs <;> ring)
  have hm : (∑ root : Window (v7RootCutoff n),
      (rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n) (Parameters.bodies_positive n)).weight root *
        integerShiftProfile n (actualCoreLaw n).weight root color) = actualRootBodyMean n color :=
    congrFun (rootProfileOperator_core n) color
  rw [hm] at hh
  exact hh

/-- The only colors whose indicator can vary under the clipped root shift. -/
def rootCoreFringe (n : ℕ) : Finset (Fin (Parameters.modulus n)) :=
  Finset.univ.filter fun color => (color.val : ℤ) ∈
    Finset.Ico ((Parameters.safeMargin n : ℤ)-v7RootCutoff n) (Parameters.safeMargin n+v7RootCutoff n) ∪
    Finset.Ico ((Parameters.safeMargin n : ℤ)+Parameters.safeSize n-v7RootCutoff n)
      (Parameters.safeMargin n+Parameters.safeSize n+v7RootCutoff n)

theorem rootCoreFringe_card (n : ℕ) : (rootCoreFringe n).card ≤ 4*v7RootCutoff n := by
  let intervals : Finset ℤ :=
    Finset.Ico ((Parameters.safeMargin n : ℤ)-v7RootCutoff n) (Parameters.safeMargin n+v7RootCutoff n) ∪
    Finset.Ico ((Parameters.safeMargin n : ℤ)+Parameters.safeSize n-v7RootCutoff n)
      (Parameters.safeMargin n+Parameters.safeSize n+v7RootCutoff n)
  have hi : (rootCoreFringe n).image (fun color => (color.val : ℤ)) ⊆ intervals := by
    intro point hp
    obtain ⟨color,hc,rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hc).2
  have hcard := Finset.card_le_card hi
  rw [Finset.card_image_of_injective _ (paletteInteger_injective n)] at hcard
  apply hcard.trans
  apply (Finset.card_union_le _ _).trans
  simp only [Int.card_Ico]
  omega

theorem rootCoreVariance_outside (n : ℕ) (color : Fin (Parameters.modulus n))
    (hout : color ∉ rootCoreFringe n) : rootCoreVariance n color = 0 := by
  have hout' : ¬ ((Parameters.safeMargin n : ℤ)-v7RootCutoff n ≤ color.val ∧
      (color.val : ℤ) < Parameters.safeMargin n+v7RootCutoff n) ∧
      ¬ ((Parameters.safeMargin n : ℤ)+Parameters.safeSize n-v7RootCutoff n ≤ color.val ∧
      (color.val : ℤ) < Parameters.safeMargin n+Parameters.safeSize n+v7RootCutoff n) := by
    simpa only [rootCoreFringe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, not_or, Finset.mem_Ico] using hout
  have hc (root : Window (v7RootCutoff n)) :
      integerShiftProfile n (actualCoreLaw n).weight root color = (actualCoreLaw n).weight color := by
    have hz := Finset.mem_Icc.mp root.property
    have he : ((color.val : ℤ)-(root : ℤ) ∈ anchorInterval (Parameters.safeMargin n) (Parameters.safeSize n)) ↔
        ((color.val : ℤ) ∈ anchorInterval (Parameters.safeMargin n) (Parameters.safeSize n)) := by
      simp only [anchorInterval, Finset.mem_Ico]
      omega
    rw [integerShiftCore_eq, ← coreIntegerProfile_on_palette n color]
    simp only [coreIntegerProfile, intervalAnchorLaw, he]
  have hm : actualRootBodyMean n color = (actualCoreLaw n).weight color := by
    rw [← rootProfileOperator_core]
    change (∑ root : Window (v7RootCutoff n), _*integerShiftProfile n _ root color) = _
    simp_rw [hc]
    rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  unfold rootCoreVariance
  simp only [hc, hm, sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, Finset.sum_const_zero]

theorem actual_root_core_deficit_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ color : Fin (Parameters.modulus n),
      1/(Parameters.safeSize n : ℝ)-actualRootBodyMean n color ≤
        4*bodyCompensation n C*actualPrimary C n (beta n) color := by
  have hmodel := ((actual_physical_supports_eventually C hC).and hbeta).mono
    (fun n h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [body_deficit_eventually C hC beta (boundaryHalf C) (bodyShift C) (bodyBlur C)
    (startsPlus C) (startsMinus C) (pairSourceShift C) (pairSourceLaw C) hmodel]
    with n hd color
  have hs : 2*Parameters.safeMargin n < Parameters.modulus n := by
    have hh := Parameters.safeSize_positive n
    unfold Parameters.safeSize at hh
    omega
  have hsize : (Parameters.safeSize n : ℝ) = (Parameters.modulus n : ℝ)-2*Parameters.safeMargin n := by
    unfold Parameters.safeSize
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hr := root_bodyMean_deficit_le_twice C n color.val hs
  have hdef := hd color
  rw [hsize]
  change 1/((Parameters.modulus n : ℝ)-2*Parameters.safeMargin n)-actualRootBodyMean n color ≤
      2*(1/((Parameters.modulus n : ℝ)-2*Parameters.safeMargin n)-actualBodyMean C n color) at hr
  change 1/((Parameters.modulus n : ℝ)-2*Parameters.safeMargin n)-actualBodyMean C n color ≤
      2*bodyCompensation n C*actualPrimary C n (beta n) color at hdef
  linarith


theorem rootCoreVariance_bounds (n : ℕ) (primary : Fin (Parameters.modulus n) → ℝ)
    (delta : ℝ) (hd : 0 ≤ delta)
    (hp : ∀ color, 1/(4*(Parameters.modulus n : ℝ)) ≤ primary color)
    (hdef : ∀ color, 1/(Parameters.safeSize n : ℝ)-actualRootBodyMean n color ≤
      4*delta*primary color) :
    (∀ color, rootCoreVariance n color / primary color^2 ≤ 32*delta) ∧
    (∑ color, rootCoreVariance n color / primary color) ≤
      32*delta*v7RootCutoff n/Parameters.modulus n := by
  have hq : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have hp0 (color) : 0 < primary color := lt_of_lt_of_le (by positivity) (hp color)
  have hb0 (color) : 0 ≤ actualRootBodyMean n color := by
    rw [← rootProfileOperator_core]
    exact rootProfileOperator_nonneg n _ (actualCoreLaw n).nonneg color
  have hbu (color) : actualRootBodyMean n color ≤ 2/(Parameters.modulus n : ℝ) := by
    rw [← rootProfileOperator_core]
    exact rootProfileOperator_bound n _ _ (by positivity) (actualCoreLaw_bounds n).1 color
  have hvar (color) : rootCoreVariance n color ≤ 4*delta*actualRootBodyMean n color*primary color := by
    rw [rootCoreVariance_identity]
    convert mul_le_mul_of_nonneg_left (hdef color) (hb0 color) using 1; ring
  have hsingle (color) : rootCoreVariance n color/primary color ≤ 8*delta/Parameters.modulus n := by
    apply (div_le_iff₀ (hp0 color)).mpr
    apply (hvar color).trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbu color) (by positivity : 0 ≤ 4*delta)) (hp0 color).le
    convert hh using 1; ring
  refine ⟨?_, ?_⟩
  · intro color
    apply (div_le_iff₀ (sq_pos_of_pos (hp0 color))).mpr
    apply (hvar color).trans
    have hbp : actualRootBodyMean n color ≤ 8*primary color := by
      have hh := mul_le_mul_of_nonneg_left (hp color) (by norm_num : (0 : ℝ) ≤ 8)
      have hh' : 2/(Parameters.modulus n : ℝ) ≤ 8*primary color := by
        convert hh using 1; ring
      exact (hbu color).trans hh'
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbp (by positivity : 0 ≤ 4*delta)) (hp0 color).le
    convert hh using 1; ring
  · have he : (∑ color, rootCoreVariance n color/primary color) =
        ∑ color ∈ rootCoreFringe n, rootCoreVariance n color/primary color := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro color _ hout
      rw [rootCoreVariance_outside n color hout, zero_div]
    rw [he]
    calc
      _ ≤ ∑ _color ∈ rootCoreFringe n, 8*delta/Parameters.modulus n :=
        Finset.sum_le_sum fun color _ => hsingle color
      _ = (rootCoreFringe n).card*(8*delta/Parameters.modulus n) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4*(v7RootCutoff n : ℝ))*(8*delta/Parameters.modulus n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast rootCoreFringe_card n) (by positivity)
      _ = _ := by ring

/-- Both the one-fixed variance and the full primary-weighted Hilbert variance
are consequences of actual calibration and actual root clipping. -/
theorem actual_root_core_variance_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      (∀ color, rootCoreVariance n color/(actualPrimary C n (beta n) color)^2 ≤ 32*bodyCompensation n C) ∧
      (∑ color, rootCoreVariance n color/actualPrimary C n (beta n) color) ≤
        32*bodyCompensation n C*v7RootCutoff n/Parameters.modulus n := by
  have hmodel := ((actual_physical_supports_eventually C hC).and hbeta).mono
    (fun n h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [actual_root_core_deficit_eventually C hC beta hbeta,
    primary_estimates_eventually C hC beta (boundaryHalf C) (bodyShift C) (bodyBlur C)
      (startsPlus C) (startsMinus C) (pairSourceShift C) (pairSourceLaw C) hmodel] with n hd hp
  have ha : 0 ≤ v7Activation C n := by
    unfold v7Activation activation
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  exact rootCoreVariance_bounds n _ _ (by unfold bodyCompensation; positivity) hp.1 hd

theorem actual_root_core_variance_power_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      (∀ color, rootCoreVariance n color/(actualPrimary C n (beta n) color)^2 ≤
        (64*(Real.exp (2*Real.pi)/1000))/(n : ℝ)^(137/4 : ℝ)) ∧
      (∑ color, rootCoreVariance n color/actualPrimary C n (beta n) color) ≤
        (192*(Real.exp (2*Real.pi)/1000))/(n : ℝ)^(289/4 : ℝ) := by
  filter_upwards [actual_root_core_variance_eventually C hC beta hbeta,
    v7Activation_upper_rpow_eventually C hC, eventually_ge_atTop 2] with n hv ha hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hd := bodyCompensation_power_bound n C hn ha
  have hq : (n : ℝ)^40 ≤ Parameters.modulus n := by
    exact_mod_cast (by simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).1)
  have hcut : (v7RootCutoff n : ℝ) ≤ 3*(n : ℝ)^2 := by
    exact_mod_cast (show v7RootCutoff n ≤ 3*n^2 by unfold v7RootCutoff; omega)
  refine ⟨?_, ?_⟩
  · intro color
    exact (hv.1 color).trans (by convert mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 32) using 1; ring)
  · apply hv.2.trans
    calc
      _ ≤ 32*((2*(Real.exp (2*Real.pi)/1000))/(n : ℝ)^(137/4 : ℝ))*(3*(n : ℝ)^2)/(n : ℝ)^40 := by
        apply div_le_div₀ (by positivity) ?_ (by positivity) hq
        exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 32)) hcut
          (by positivity) (by positivity)
      _ = _ := by
        have he : (n : ℝ)^(289/4 : ℝ) = (n : ℝ)^(137/4 : ℝ)*(n : ℝ)^38 := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
          norm_num
        rw [he]
        field_simp
        ring

end
end AFT.V7Calibration

import AFT.RootProfileChannel
import AFT.RootAnchorResponse
import AFT.OrdinaryRootVariance

/-! # Calibration-preserving variance of the actual ordinary-root body -/

namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

def integerTranslateLinear (n : ℕ) (shift : ℤ) : Module.End ℝ (Fin (Parameters.modulus n) → ℝ) where
  toFun profile := integerShiftProfile n profile shift
  map_add' first second := by
    funext color
    simp only [integerShiftProfile,Pi.add_apply]
    calc
      _ = ∑ center, ((if (color.val : ℤ) = (center.val : ℤ)+shift then first center else 0) +
          (if (color.val : ℤ) = (center.val : ℤ)+shift then second center else 0)) := by
        apply Finset.sum_congr rfl
        intro center _
        split_ifs <;> ring
      _ = _ := Finset.sum_add_distrib
  map_smul' scalar profile := by
    funext color
    exact integerShiftProfile_smul n profile scalar shift color

def rootCenteredShift (n : ℕ) (root : Window (v7RootCutoff n)) : Module.End ℝ (Fin (Parameters.modulus n) → ℝ) :=
  integerTranslateLinear n root - rootProfileOperator n

def rootBodyVariance (n : ℕ) (profile : Fin (Parameters.modulus n) → ℝ) (color : Fin (Parameters.modulus n)) : ℝ :=
  ∑ root, (bodyRootReference n).weight root * (rootCenteredShift n root profile color)^2

theorem rootBodyVariance_core (n : ℕ) (color : Fin (Parameters.modulus n)) :
    rootBodyVariance n (actualCoreLaw n).weight color = rootCoreVariance n color := by
  simp only [rootBodyVariance,rootCenteredShift,LinearMap.sub_apply,Pi.sub_apply,
    integerTranslateLinear,LinearMap.coe_mk,AddHom.coe_mk,rootProfileOperator_core]
  rfl

theorem rootBodyVariance_profile_energy (n : ℕ) (reference profile : Fin (Parameters.modulus n) → ℝ) :
    (∑ color, rootBodyVariance n profile color / reference color) =
      ∑ root, (bodyRootReference n).weight root * profileSquareNorm reference (rootCenteredShift n root profile) := by
  simp only [rootBodyVariance,Finset.sum_div,profileSquareNorm,Finset.mul_sum,mul_div_assoc]
  exact Finset.sum_comm

theorem rootBodyVariance_combination (n : ℕ) (first second : Fin (Parameters.modulus n) → ℝ)
    (a b : ℝ) (color : Fin (Parameters.modulus n)) :
    rootBodyVariance n (a • first - b • second) color ≤
      2*a^2*rootBodyVariance n first color + 2*b^2*rootBodyVariance n second color := by
  simp only [rootBodyVariance,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro root _
  have hh : (a*rootCenteredShift n root first color-b*rootCenteredShift n root second color)^2 ≤
      2*a^2*(rootCenteredShift n root first color)^2+2*b^2*(rootCenteredShift n root second color)^2 := by
    nlinarith [sq_nonneg (a*rootCenteredShift n root first color+b*rootCenteredShift n root second color)]
  exact (mul_le_mul_of_nonneg_left hh (FiniteDist.nonneg _ _)).trans_eq (by ring)

theorem rootCenteredShift_anchor (n : ℕ) (profile : Fin (Parameters.modulus n) → ℝ)
    (root : Window (v7RootCutoff n)) (color : Fin (Parameters.modulus n)) :
    rootCenteredShift n root (publicAnchorFiniteProfile n profile) color =
      integerAnchorDifferenceProfile n root profile color -
        ∑ other, (bodyRootReference n).weight other * integerAnchorDifferenceProfile n other profile color := by
  change integerShiftProfile n (publicAnchorFiniteProfile n profile) root color -
    (∑ other, (bodyRootReference n).weight other * integerShiftProfile n (publicAnchorFiniteProfile n profile) other color) = _
  simp only [shifted_publicAnchorFiniteProfile,integerAnchorDifferenceProfile,Pi.sub_apply,
    mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,FiniteDist.sum_one,one_mul]
  ring

/-- The actual primary average is fed into the actual finite two-interval
anchor before taking the root variance. -/
theorem actual_root_anchor_variance_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      (∀ color, rootBodyVariance n (publicAnchorFiniteProfile n (actualPrimaryLaw C n (beta n)).weight) color /
        (actualPrimaryLaw C n (beta n)).weight color^2 ≤ 256*(n : ℝ)^16) ∧
      (∑ color, rootBodyVariance n (publicAnchorFiniteProfile n (actualPrimaryLaw C n (beta n)).weight) color /
        (actualPrimaryLaw C n (beta n)).weight color) ≤ 192/(n : ℝ)^22 := by
  filter_upwards [actual_root_anchor_difference_eventually C hC beta hbeta]
    with n hb
  let primary := actualPrimaryLaw C n (beta n)
  let difference := fun root : Window (v7RootCutoff n) => integerAnchorDifferenceProfile n root primary.weight
  have hself : profileSquareNorm primary.weight primary.weight = 1 := by
    calc
      _ = ∑ color, primary.weight color := by
        apply Finset.sum_congr rfl
        intro color _
        change primary.weight color ^ 2 / primary.weight color = primary.weight color
        by_cases hz : primary.weight color = 0
        · simp only [hz,zero_pow (by norm_num : (2 : ℕ) ≠ 0),div_zero]
        · field_simp
      _ = 1 := primary.sum_one
  have hroot (root : Window (v7RootCutoff n)) : |(root : ℤ)| ≤ (v7RootCutoff n : ℤ) :=
    abs_le.mpr (Finset.mem_Icc.mp root.property)
  have hfull (root) : profileSquareNorm primary.weight (difference root) ≤ 48/(n : ℝ)^22 := by
    have hh := (hb root (hroot root) primary.weight).1
    change profileSquareNorm primary.weight (difference root) ≤ (48/(n : ℝ)^22)*profileSquareNorm primary.weight primary.weight at hh
    simpa only [hself,mul_one] using hh
  have hrow (root) (color) : |difference root color/primary.weight color| ≤ 8*(n : ℝ)^8 := by
    have hh := (hb root (hroot root) primary.weight).2 color
    change |difference root color/primary.weight color| ≤ 8*(n : ℝ)^8*Real.sqrt (profileSquareNorm primary.weight primary.weight) at hh
    simpa only [hself,Real.sqrt_one,mul_one] using hh
  have hcenter (root) : profileSquareNorm primary.weight
      (rootCenteredShift n root (publicAnchorFiniteProfile n primary.weight)) ≤ 192/(n : ℝ)^22 := by
    have hh := centeredFamily_profile_energy_le (bodyRootReference n) primary.weight 0 difference
      (48/(n : ℝ)^22) primary.nonneg (fun point => by simpa only [sub_zero] using hfull point) root
    have heq : (rootCenteredShift n root (publicAnchorFiniteProfile n primary.weight)) =
        (fun color => difference root color - ∑ other, (bodyRootReference n).weight other * difference other color) :=
      funext (rootCenteredShift_anchor n primary.weight root)
    rw [heq]
    exact hh.trans_eq (by ring)
  constructor
  · intro color
    have hmean : |∑ other, (bodyRootReference n).weight other * (difference other color/primary.weight color)| ≤ 8*(n : ℝ)^8 := by
      calc
        _ ≤ ∑ other, |(bodyRootReference n).weight other * (difference other color/primary.weight color)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ other, (bodyRootReference n).weight other * |difference other color/primary.weight color| := by
          apply Finset.sum_congr rfl
          intro other _
          rw [abs_mul,abs_of_nonneg (FiniteDist.nonneg _ _)]
        _ ≤ ∑ other, (bodyRootReference n).weight other * (8*(n : ℝ)^8) :=
          Finset.sum_le_sum fun other _ => mul_le_mul_of_nonneg_left (hrow other color) (FiniteDist.nonneg _ _)
        _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]
    have hpoint (root) : (rootCenteredShift n root (publicAnchorFiniteProfile n primary.weight) color / primary.weight color)^2 ≤ 256*(n : ℝ)^16 := by
      rw [rootCenteredShift_anchor,sub_div,Finset.sum_div]
      have heq : (∑ other, (bodyRootReference n).weight other * difference other color / primary.weight color) =
          ∑ other, (bodyRootReference n).weight other * (difference other color / primary.weight color) := by
        apply Finset.sum_congr rfl
        intro other _
        ring
      change (difference root color / primary.weight color - ∑ other, (bodyRootReference n).weight other * difference other color / primary.weight color)^2 ≤ _
      rw [heq]
      have hh : |difference root color / primary.weight color - ∑ other,
          (bodyRootReference n).weight other * (difference other color/primary.weight color)| ≤ 16*(n : ℝ)^8 :=
        (by
          have habs := abs_sub_le (difference root color / primary.weight color) 0
            (∑ other, (bodyRootReference n).weight other * (difference other color / primary.weight color))
          simp only [sub_zero,zero_sub,abs_neg] at habs
          linarith [hrow root color])
      have hh' := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
      norm_num only [sq_abs,mul_pow,← pow_mul] at hh'
      exact hh'
    unfold rootBodyVariance
    rw [Finset.sum_div]
    calc
      _ = ∑ root, (bodyRootReference n).weight root *
          (rootCenteredShift n root (publicAnchorFiniteProfile n primary.weight) color / primary.weight color)^2 := by
        apply Finset.sum_congr rfl
        intro root _
        rw [div_pow]
        ring
      _ ≤ ∑ root, (bodyRootReference n).weight root * (256*(n : ℝ)^16) :=
        Finset.sum_le_sum fun root _ => mul_le_mul_of_nonneg_left (hpoint root) (FiniteDist.nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]
  · rw [rootBodyVariance_profile_energy]
    calc
      _ ≤ ∑ root, (bodyRootReference n).weight root * (192/(n : ℝ)^22) :=
        Finset.sum_le_sum fun root _ => mul_le_mul_of_nonneg_left (hcenter root) (FiniteDist.nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]


theorem actualBodyCenter_calibrated (C : ℝ) (n : ℕ) (beta : ℝ) :
    actualBodyCenter C n beta =
      (1+bodyCompensation n C) • (actualCoreLaw n).weight -
        bodyCompensation n C • publicAnchorFiniteProfile n (actualPrimary C n beta) := by
  funext color
  simp only [actualBodyCenter,calibratedBodyProfile,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,publicAnchorFiniteProfile,applyAnchor,anchorMean]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro input _
  ring

/-- This is the variance of the actual calibrated body, not just its core.
The small retained deficit and the translated primary anchor are both
included with their original compensation coefficients. -/
theorem actual_root_body_variance_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      (∀ color, rootBodyVariance n (actualBodyCenter C n (beta n)) color /
        (actualPrimaryLaw C n (beta n)).weight color^2 ≤
        64*(1+bodyCompensation n C)^2*bodyCompensation n C +
          512*(bodyCompensation n C)^2*(n : ℝ)^16) ∧
      (∑ color, rootBodyVariance n (actualBodyCenter C n (beta n)) color /
        (actualPrimaryLaw C n (beta n)).weight color) ≤
        64*(1+bodyCompensation n C)^2*bodyCompensation n C*v7RootCutoff n/Parameters.modulus n +
          384*(bodyCompensation n C)^2/(n : ℝ)^22 := by
  filter_upwards [actual_root_core_variance_eventually C hC beta hbeta,
    actual_root_anchor_variance_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta]
    with n hc ha hl
  let primary := actualPrimaryLaw C n (beta n)
  let delta := bodyCompensation n C
  have heq : actualBodyCenter C n (beta n) =
      (1+delta) • (actualCoreLaw n).weight - delta • publicAnchorFiniteProfile n primary.weight := by
    rw [actualBodyCenter_calibrated]
    change _ = (1+delta) • (actualCoreLaw n).weight - delta • publicAnchorFiniteProfile n (actualPrimaryLaw C n (beta n)).weight
    rw [hl.1]
  have hpoint := rootBodyVariance_combination n (actualCoreLaw n).weight
    (publicAnchorFiniteProfile n primary.weight) (1+delta) delta
  rw [← heq] at hpoint
  constructor
  · intro color
    have hmain := div_le_div_of_nonneg_right (hpoint color) (sq_nonneg (primary.weight color))
    have hcore := hc.1 color
    have hanchor := ha.1 color
    have hpEq : primary.weight color = actualPrimary C n (beta n) color := congrFun hl.1 color
    rw [← hpEq] at hcore
    simp only [rootBodyVariance_core,add_div,mul_div_assoc] at hmain
    apply hmain.trans
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left hcore (show 0 ≤ 2*(1+delta)^2 by positivity))
      (mul_le_mul_of_nonneg_left hanchor (show 0 ≤ 2*delta^2 by positivity))
    exact hh.trans_eq (by change _ = 64*(1+delta)^2*delta+512*delta^2*(n : ℝ)^16; ring)
  · have hmain : (∑ color, rootBodyVariance n (actualBodyCenter C n (beta n)) color / primary.weight color) ≤
        2*(1+delta)^2*(∑ color,rootCoreVariance n color/primary.weight color) +
        2*delta^2*(∑ color,rootBodyVariance n (publicAnchorFiniteProfile n primary.weight) color/primary.weight color) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro color _
      simpa only [rootBodyVariance_core,add_div,mul_div_assoc] using
        div_le_div_of_nonneg_right (hpoint color) (primary.nonneg color)
    have hcore := hc.2
    have hpEq : primary.weight = actualPrimary C n (beta n) := hl.1
    rw [← hpEq] at hcore
    apply hmain.trans
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left hcore (show 0 ≤ 2*(1+delta)^2 by positivity))
      (mul_le_mul_of_nonneg_left ha.2 (show 0 ≤ 2*delta^2 by positivity))
    exact hh.trans_eq (by
      change _ = 64*(1+delta)^2*delta*v7RootCutoff n/Parameters.modulus n+384*delta^2/(n : ℝ)^22
      ring)

end
end AFT.V7Calibration

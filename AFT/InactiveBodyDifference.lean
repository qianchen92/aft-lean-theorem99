import AFT.AttachedBodyDifference

/-! # Centering against the exact inactive attachment-source law -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def inactiveAttachedBodyDifference (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue source : ℤ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  attachedBodyAtSource cutoffScale parameter beta queue source - averagedInactiveBody cutoffScale parameter beta queue

def inactiveAttachedBodyDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue source : ℤ)
    (color : Fin (Parameters.modulus parameter)) : ℝ :=
  inactiveAttachedBodyDifference cutoffScale parameter beta queue source color / actualPrimary cutoffScale parameter beta color

theorem inactiveAttachedBodyDifference_average (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue source : ℤ)
    (color : Fin (Parameters.modulus parameter)) :
    inactiveAttachedBodyDifference cutoffScale parameter beta queue source color =
      ∑ other, (inactiveLegSource cutoffScale parameter).weight other *
        (attachedBodyAtSource cutoffScale parameter beta queue source color -
          attachedBodyAtSource cutoffScale parameter beta queue other color) := by
  simp only [inactiveAttachedBodyDifference, Pi.sub_apply, averagedInactiveBody, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem inactive_source_difference_bound (cutoffScale : ℝ) (parameter : ℕ)
    (first second : Window (legCutoff cutoffScale parameter - 1)) :
    (((first : ℤ) - second).natAbs : ℝ) ≤ 2 * (legCutoff cutoffScale parameter : ℝ) := by
  have hf := abs_le.mpr (Finset.mem_Icc.mp first.property)
  have hs := abs_le.mpr (Finset.mem_Icc.mp second.property)
  have hh := abs_sub (first : ℤ) (second : ℤ)
  have hab : |(first : ℤ) - second| ≤ 2 * (legCutoff cutoffScale parameter : ℤ) := by omega
  have hnat : ((first : ℤ) - second).natAbs ≤ 2 * legCutoff cutoffScale parameter := by
    exact_mod_cast (show (((first : ℤ) - second).natAbs : ℤ) ≤ 2 * (legCutoff cutoffScale parameter : ℤ) by simpa only [Int.natCast_natAbs] using hab)
  exact_mod_cast hnat

/-- Full and fixed-coordinate bounds use the literal inactive conditional
source. The endpoint and body retain their shared source value. -/
theorem actual_inactive_body_difference_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ queue : ℤ, ∀ source : Window (legCutoff cutoffScale parameter - 1),
      (∀ color, |inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source color| ≤ 16) ∧
      (∑ color, actualPrimary cutoffScale parameter (beta parameter) color *
        inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source color ^ 2) ≤
        384 * (legCutoff cutoffScale parameter : ℝ) / Parameters.modulus parameter := by
  filter_upwards [actual_attached_body_source_difference_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 1]
    with parameter hd hp hlarge queue source
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let difference := inactiveAttachedBodyDifference cutoffScale parameter (beta parameter) queue source
  let nu := inactiveLegSource cutoffScale parameter
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hrelative (color) : |difference color| ≤ 16 * p color := by
    dsimp only [difference]
    rw [inactiveAttachedBodyDifference_average]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ other, nu.weight other * (16 * p color) := by
        apply Finset.sum_le_sum
        intro other _
        rw [abs_mul, abs_of_nonneg (nu.nonneg other)]
        exact mul_le_mul_of_nonneg_left ((hd queue source other).1 color) (nu.nonneg other)
      _ = _ := by rw [← Finset.sum_mul, nu.sum_one, one_mul]
  have hL1 : (∑ color, |difference color|) ≤ 24 * (legCutoff cutoffScale parameter : ℝ) / Parameters.modulus parameter := by
    calc
      _ ≤ ∑ color, ∑ other, nu.weight other *
          |attachedBodyAtSource cutoffScale parameter (beta parameter) queue source color -
            attachedBodyAtSource cutoffScale parameter (beta parameter) queue other color| := by
        apply Finset.sum_le_sum
        intro color _
        dsimp only [difference]
        rw [inactiveAttachedBodyDifference_average]
        exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
          apply Finset.sum_congr rfl
          intro other _
          rw [abs_mul, abs_of_nonneg (nu.nonneg other)])
      _ = ∑ other, nu.weight other * ∑ color,
          |attachedBodyAtSource cutoffScale parameter (beta parameter) queue source color -
            attachedBodyAtSource cutoffScale parameter (beta parameter) queue other color| := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ ∑ other, nu.weight other * (24 * (legCutoff cutoffScale parameter : ℝ) / Parameters.modulus parameter) := by
        apply Finset.sum_le_sum
        intro other _
        apply mul_le_mul_of_nonneg_left _ (nu.nonneg other)
        have hh := attachedBodyAtSource_difference_l1 cutoffScale parameter (beta parameter) hscale hlarge
          (fun color => (hp.1 color).le) hp.2 queue source other
        have hb := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (inactive_source_difference_bound cutoffScale parameter source other) (by norm_num : (0 : ℝ) ≤ 12)) hq.le
        exact hh.trans (hb.trans_eq (by ring))
      _ = _ := by rw [← Finset.sum_mul, nu.sum_one, one_mul]
  have hnorm := profileSquareNorm_le_relative_mul_l1 p difference 16 hp.1 hrelative
  refine ⟨?_, ?_⟩
  · intro color
    unfold inactiveAttachedBodyDensity
    rw [abs_div, abs_of_pos (hp.1 color)]
    exact (div_le_iff₀ (hp.1 color)).mpr (hrelative color)
  · have heq : (∑ color, actualPrimary cutoffScale parameter (beta parameter) color *
        inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue source color ^ 2) =
        profileSquareNorm p difference := by
      apply Finset.sum_congr rfl
      intro color _
      change p color * (difference color / p color)^2 = difference color ^ 2 / p color
      field_simp [ne_of_gt (hp.1 color)]
    rw [heq]
    exact hnorm.trans ((mul_le_mul_of_nonneg_left hL1 (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

/-- All centered inactive body profiles have zero total mass in the actual
queue window, after the remaining root source is included. -/
theorem actual_inactive_body_canonical_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ queue : ℤ, |queue| ≤ queueCutoff parameter →
      ∀ source : Window (legCutoff cutoffScale parameter - 1),
        (∑ color, inactiveAttachedBodyDifference cutoffScale parameter (beta parameter) queue source color) = 0 := by
  filter_upwards [actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    legCutoff_le_square_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hb hcut hp queue hqueue source
  have hmass (other : Window (legCutoff cutoffScale parameter - 1)) :
      (∑ color, attachedBodyAtSource cutoffScale parameter (beta parameter) queue other color) = 1 := by
    apply attachedBodyAtSource_mass cutoffScale parameter (beta parameter) hb.1 hb.2.2
    have hs := abs_le.mpr (Finset.mem_Icc.mp other.property)
    have ha := abs_add_le (other : ℤ) queue
    have hc : legCutoff cutoffScale parameter ≤ parameter^2 := hcut
    simp only [queueCutoff, Parameters.safeMargin, Parameters.security_eq parameter hp, v7RootCutoff] at *
    omega
  simp only [inactiveAttachedBodyDifference, Pi.sub_apply, Finset.sum_sub_distrib, hmass]
  unfold averagedInactiveBody
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hmass, mul_one]
  rw [FiniteDist.sum_one, sub_self]

end
end AFT.V7Calibration

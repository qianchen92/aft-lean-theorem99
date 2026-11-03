import AFT.GlobalMeanOutput

/-! # Actual probability masses of the root-marginalized local blocks -/
namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section

theorem actual_local_pair_mass_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, (∑ first,∑ second,localPairMixture C n (beta n) first second) = 1 := by
  filter_upwards [actual_pair_branch_mixture_eventually C hC beta hbeta] with n hm
  simp_rw [← hm]
  rw [← Fintype.sum_prod_type]
  exact FiniteDist.sum_one _

theorem actual_attached_body_mass_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      ∀ source : Window (legCutoff C n-1), (∑ color,attachedBodyAtSource C n (beta n) queue source color) = 1 := by
  filter_upwards [actual_body_center_probability_eventually C hC beta hbeta,
    legCutoff_le_square_eventually C hC,eventually_ge_atTop 2] with n hb hcut hn queue hq source
  apply attachedBodyAtSource_mass C n (beta n) hb.1 hb.2.2
  have hs := abs_le.mpr (Finset.mem_Icc.mp source.property)
  have ha := abs_add_le (source : ℤ) queue
  simp only [queueCutoff,Parameters.safeMargin,Parameters.security_eq n hn,v7RootCutoff] at *
  omega

theorem actual_local_body_mass_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      (∑ color,localBodyMixture C n (beta n) queue color) = 1 := by
  filter_upwards [actual_attached_body_mass_eventually C hC beta hbeta] with n hb queue hq
  simp_rw [localBodyMixture_source_average]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,hb queue hq,mul_one]
  exact FiniteDist.sum_one _

theorem actual_block_body_mass_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ index : blockIndex n, ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      (∑ color,blockBodyMeanProfile C n (beta n) index queue color) = 1 := by
  filter_upwards [actual_attached_body_mass_eventually C hC beta hbeta,
    actual_local_body_mass_eventually C hC beta hbeta] with n ha hb index queue hq
  cases index with
  | inl _ => exact hb queue hq
  | inr _ => exact ha queue hq (windowZero (legCutoff C n-1))

end
end AFT.V7Calibration

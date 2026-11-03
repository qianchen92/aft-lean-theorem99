import AFT.ActualBetaReference
import AFT.FiniteProductVariation

/-! # Full reference-histogram stability under finite beta rounding -/
namespace AFT.BetaReference
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance referenceVariationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance referenceVariationSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

theorem convexLaw_l1_le (interior boundary : FiniteDist Color) (theta eta : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (he0 : 0 ≤ eta) (he1 : eta ≤ 1) :
    (∑ color,|(convexLaw interior boundary theta ht0 ht1).weight color-
      (convexLaw interior boundary eta he0 he1).weight color|) ≤ 2*|theta-eta| := by
  have heq (color) : (convexLaw interior boundary theta ht0 ht1).weight color-
      (convexLaw interior boundary eta he0 he1).weight color=
      (theta-eta)*(boundary.weight color-interior.weight color) := by unfold convexLaw; ring
  simp_rw [heq,abs_mul]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (FiniteDist.l1_distance_le_two boundary interior) (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- Every count, including the full histogram tail, is compared under the
same literal finite product of the two actual color populations. -/
theorem referenceHistogram_l1_le (N K : ℕ) (hKN : K ≤ N) (interior boundary : FiniteDist Color)
    (theta eta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (he0 : 0 ≤ eta) (he1 : eta ≤ 1) :
    (∑ hist,|(referenceHistogram N K hKN interior boundary theta).weight hist-
      (referenceHistogram N K hKN interior boundary eta).weight hist|) ≤ 2*K*|theta-eta| := by
  rw [referenceHistogram,referenceHistogram,dif_pos ⟨ht0,ht1⟩,dif_pos ⟨he0,he1⟩]
  apply (FiniteDist.l1_map_le _ _ _).trans
  have hp := FiniteDist.l1_sumtype_common_le interior (convexLaw interior boundary theta ht0 ht1)
    (convexLaw interior boundary eta he0 he1) (N-K) K
  have hbound := hp.trans ((mul_le_mul_of_nonneg_left
    (convexLaw_l1_le interior boundary theta eta ht0 ht1 he0 he1)
    (Nat.cast_nonneg K)).trans_eq (show (K : ℝ)*(2*|theta-eta|)=2*K*|theta-eta| by ring))
  convert hbound using 1
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rfl

/-- Uniform Lipschitz bound over the entire legal beta interval. -/
theorem inverseBeta_histogram_l1_le (N K : ℕ) (hKN : K ≤ N) (interior boundary : FiniteDist Color)
    (b cutoff beta gamma : ℝ) (hb : 0 ≤ b) (hc : 0 < cutoff) (hbc : b ≤ cutoff)
    (hbeta : cutoff ≤ beta) (hgamma : cutoff ≤ gamma) :
    (∑ hist,|(referenceHistogram N K hKN interior boundary (b/beta)).weight hist-
      (referenceHistogram N K hKN interior boundary (b/gamma)).weight hist|) ≤
        2*K*b*|beta-gamma|/cutoff^2 := by
  have hbp := hc.trans_le hbeta
  have hgp := hc.trans_le hgamma
  have ht := referenceHistogram_l1_le N K hKN interior boundary (b/beta) (b/gamma)
    (div_nonneg hb hbp.le) ((div_le_one hbp).mpr (hbc.trans hbeta))
    (div_nonneg hb hgp.le) ((div_le_one hgp).mpr (hbc.trans hgamma))
  have he : b/beta-b/gamma=b*(gamma-beta)/(beta*gamma) := by field_simp
  rw [he,abs_div,abs_mul,abs_of_nonneg hb,abs_of_pos (mul_pos hbp hgp),abs_sub_comm] at ht
  have hden : cutoff^2 ≤ beta*gamma := by
    rw [pow_two]
    exact mul_le_mul hbeta hgamma hc.le hbp.le
  have hd := div_le_div_of_nonneg_left (mul_nonneg hb (abs_nonneg (beta-gamma))) (pow_pos hc 2) hden
  exact ht.trans ((mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2*K)).trans_eq (by ring))

end
end AFT.BetaReference

namespace AFT.V7Calibration
noncomputable local instance actualReferenceVariationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
open GaussianSource BetaReference Filter
open scoped BigOperators Classical Topology
noncomputable section

theorem actual_reference_histogram_l1_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,∀ beta gamma : ℝ,actualBetaCutoff C n ≤ beta → actualBetaCutoff C n ≤ gamma →
      (∑ hist,|(actualPositiveReferenceHistogram C n beta).weight hist-
        (actualPositiveReferenceHistogram C n gamma).weight hist|) ≤
          2*Parameters.legs n*actualBoundaryFraction C n*|beta-gamma|/(actualBetaCutoff C n)^2 := by
  filter_upwards [actual_reference_histogram_eventually C hC,actual_beta_cutoff_eventually C hC]
    with n href hc beta gamma hb hg
  rw [href beta hb,href gamma hg]
  exact inverseBeta_histogram_l1_le _ _ _ _ _ _ _ _ _ (by unfold actualBoundaryFraction; positivity) hc.1 hc.2.1 hb hg

end
end AFT.V7Calibration

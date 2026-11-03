import AFT.PairedTableMean
import AFT.ActualPairedPublic

/-! # Actual complete paired control-table moments -/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualPairedTableMomentSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

/-- All hypotheses of the complete paired-table moment theorem are
supplied by the actual Gaussian calibration and public anchor. -/
theorem actual_paired_table_moments_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ) / (2 * Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2 * (Parameters.legs n : ℝ) / Parameters.dimension n) :
    ∀ᶠ n in atTop,
      ∀ primaryPool bodyPool : ℕ, 0 < primaryPool → 0 < bodyPool →
      ∀ radius : ℝ, 1 ≤ radius →
      ∀ table : Table (InputSeed (Fin (Parameters.modulus n))),
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) table →
      ∀ order : ℕ, (∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order) →
      2 * order ≤ primaryPool → 2 * order ≤ bodyPool →
      ∀ moment : ℕ, 0 < moment →
      (FiniteDist.independent (Sum.elim
        (fun _ : Fin primaryPool => (actualPrimaryLaw C n (beta n)).prod (actualBodyLaw C n (beta n)))
        (fun _ : Fin bodyPool => (actualPrimaryLaw C n (beta n)).prod (actualBodyLaw C n (beta n))))).expectation
        (fun word => |tablePairedStatistic (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (fun color center => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val)
          (v7Activation C n) primaryPool bodyPool table word|^(2 * moment)) ≤
        (representedPairedMomentConstant 772 order moment *
          activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool radius) table)^(2 * moment) := by
  filter_upwards [actual_public_anchor_comparison_eventually C hC beta hbeta,
    actual_anchor_supported_eventually C hC beta hbeta, eventually_ge_atTop 2]
    with n hcompare hs hn primaryPool bodyPool hp hb radius hr table hc order ho hpl hbl moment hm
  have hsupport (point center : Fin (Parameters.modulus n)) (hz : (actualBodyLaw C n (beta n)).weight center = 0) :
      publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) point center.val = 0 := by
    have hh := hs (Pi.single point 1) center hz
    simpa [applyAnchor, Pi.single_apply] using hh
  exact tablePairedStatistic_even_moment (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    _ (v7Activation C n) 772
    (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).le
    (activation_le_one _ _ _ _) (by norm_num) (fun color center => publicAnchorKernel_nonneg _ _ _ _)
    (fun color => (actual_anchor_safe_mass n color).1) hcompare hsupport primaryPool bodyPool hp hb
    radius hr table hc order ho hpl hbl moment hm
end
end AFT.V7Calibration

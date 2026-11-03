import AFT.RootWindow
import AFT.RootGaussianApprox
import AFT.ProjectionError

/-!
# Canonical bounds for the actual protected root marginals

This module joins the exact finite marginal formula, the proved convolution
error, the actual marginal moment, and the canonical Taylor estimate.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable section

local instance (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def rootPrefixDensity (width : ℝ) (cutoff selected remaining : ℕ)
    (hn : 0 < selected + remaining) (x : Fin selected → Window cutoff) : ℝ :=
  (RootSlice.prefixLaw (windowGaussian width cutoff) (fun z => (z : ℤ)) selected remaining
    (window_root_probability_positive width cutoff (selected + remaining))).weight x /
      (FiniteDist.independent (fun _ : Fin selected =>
        rootMarginal width cutoff (selected + remaining) hn)).weight x

theorem rootPrefixDensity_ratio (width : ℝ) (cutoff selected remaining : ℕ)
    (hk : 0 < selected) (hn : 2 ≤ selected + remaining) (x : Fin selected → Window cutoff) :
    rootPrefixDensity width cutoff selected remaining (by omega) x =
      rootProbability width cutoff remaining (-∑ i, (x i : ℤ)) *
        rootProbability width cutoff (selected + remaining) 0 ^ (selected - 1) /
        ∏ i, rootProbability width cutoff (selected + remaining - 1) (-(x i : ℤ)) := by
  exact RootSlice.prefix_density_ratio (windowGaussian width cutoff) (fun z => (z : ℤ))
    selected remaining hk (window_root_probability_positive width cutoff (selected + remaining))
    (windowGaussian_positive width cutoff)
    (window_sum_probability_positive width cutoff (selected + remaining - 1) (by omega)) x

theorem rootModelPrefactor_positive (width normalization : ℝ) (population order : ℕ)
    (hw : 0 < width) (hz : 0 < normalization) (hk : 0 < order) (hn : order < population) :
    0 < rootModelPrefactor width normalization population order := by
  rw [rootModelPrefactor_eq width normalization population order hw hz hn hk]
  have hp : 0 < population := by omega
  have hp1 : 0 < population - 1 := by omega
  have hrem : 0 < population - order := by omega
  positivity

/-- A finite, explicit bound for the actual root ANOVA kernel. The scalar
convolution errors are the formulas already proved for the clipped source;
there is no assumed probabilistic Gaussian approximation. -/
theorem rootPrefixDensity_anova_bound (width thetaBound error : ℝ)
    (cutoff selected remaining : ℕ) (hk : 0 < selected)
    (hhalf : 2 * selected ≤ selected + remaining)
    (hw : 1 ≤ width) (hcutoff : ⌊width⌋₊ ≤ cutoff)
    (ht0 : 0 ≤ thetaBound) (ht1 : thetaBound ≤ 1)
    (ht : thetaError (width / Real.sqrt 2) ≤ thetaBound)
    (he0 : 0 ≤ error) (he1 : error < 1)
    (hsmall : 4 * (((selected : ℝ) + 1) / (selected + remaining)) ≤ (1 / 4 : ℝ))
    (hcompare : ∀ a, (rootMarginal width cutoff (selected + remaining) (by omega)).weight a ≤
      4 * (windowGaussian width cutoff).weight a)
    (hremaining : ∀ x : Fin selected → Window cutoff,
      rootSumError width thetaBound cutoff (remaining - 1) (-∑ i, (x i : ℤ)) ≤ error)
    (hroot : rootSumError width thetaBound cutoff (selected + remaining - 1) 0 ≤ error)
    (hmarginal : ∀ a : Window cutoff,
      rootSumError width thetaBound cutoff (selected + remaining - 1 - 1) (-(a : ℤ)) ≤ error) :
    let p := fun _ : Fin selected => rootMarginal width cutoff (selected + remaining) (by omega)
    let c := rootModelPrefactor width (realNormalizer width) (selected + remaining) selected
    let bound := 4 * ((1 + 2 / Real.pi) * Real.sqrt 2 * Real.exp Real.pi)
    let order := (selected + 1) / 2
    (FiniteDist.independent p).l2Sq (Hoeffding.projection p Finset.univ
      (rootPrefixDensity width cutoff selected remaining (by omega))) ≤
      2 * c ^ 2 *
        ((((selected : ℝ) + 1) / (selected + remaining)) ^ (2 * order) *
          (((2 * order).factorial : ℝ) / (1 / 8 : ℝ) ^ (2 * order)) * bound ^ selected) +
        2 * (c * ratioError error selected) ^ 2 * bound ^ selected := by
  have hw0 : 0 < width := by linarith
  have hn : 2 ≤ selected + remaining := by omega
  have hz : 0 < realNormalizer width := zero_lt_one.trans_le (realNormalizer_ge_one width hw0)
  have happrox (x : Fin selected → Window cutoff) :
      |rootPrefixDensity width cutoff selected remaining (by omega) x /
        (rootModelPrefactor width (realNormalizer width) (selected + remaining) selected *
          Real.exp (MvPolynomial.eval (fun i => normalizedRoot width (x i))
            (RootSlice.quadraticExponent (selected + remaining)))) - 1| ≤
        ratioError error selected := by
    have hh := root_probability_ratio_error width thetaBound error cutoff
      (selected + remaining) selected hw0 (by omega) hk ht0 ht1 ht he0 he1
      (fun i => (x i : ℤ)) (by simpa using hremaining x) hroot (fun i => hmarginal (x i))
    rw [rootPrefixDensity_ratio width cutoff selected remaining hk hn]
    rw [rootExponent_eq_quadratic] at hh
    simpa [normalizedRoot] using hh
  have h := RootSlice.quadratic_approximation_anova_bound
    (selected + remaining) (1 / 4) (4 * ((1 + 2 / Real.pi) * Real.sqrt 2 * Real.exp Real.pi))
    (rootModelPrefactor width (realNormalizer width) (selected + remaining) selected)
    (ratioError error selected)
    (fun _ : Fin selected => rootMarginal width cutoff (selected + remaining) (by omega))
    (fun _ a => rootMarginal_positive width cutoff (selected + remaining) hn a)
    (fun _ a => normalizedRoot width a)
    (rootPrefixDensity width cutoff selected remaining (by omega))
    (by exact_mod_cast hn)
    (by simpa using (show 2 * (selected : ℝ) ≤ selected + remaining by exact_mod_cast hhalf))
    (by norm_num)
    (rootModelPrefactor_positive width (realNormalizer width) (selected + remaining) selected
      hw0 hz hk (by omega))
    (by simpa using hsmall)
    (fun _ => rootMarginal_exp_square width 4 cutoff (selected + remaining) (by omega)
      hw hcutoff (by norm_num) hcompare) happrox
  simpa only [Fintype.card_fin, show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] using h

end

end AFT.GaussianSource

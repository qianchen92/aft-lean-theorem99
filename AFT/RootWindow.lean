import AFT.RootMarginal
import AFT.GaussianMoments

/-!
# Positive marginals and moments on the actual protected root alphabet
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable section

local instance (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def windowNegate (cutoff : ℕ) (a : Window cutoff) : Window cutoff :=
  ⟨-(a : ℤ), by
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp a.property
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- A single protected value can be balanced by one remaining coordinate.
Thus all the denominators in the marginal quotient are strictly positive. -/
theorem window_sum_probability_positive (width : ℝ) (cutoff count : ℕ)
    (hc : 0 < count) (a : Window cutoff) :
    0 < RootSlice.sumProbability (windowGaussian width cutoff) (fun z => (z : ℤ))
      count (-(a : ℤ)) := by
  let first : Fin count := ⟨0, hc⟩
  let configuration : Fin count → Window cutoff :=
    fun i => if i = first then windowNegate cutoff a else windowZero cutoff
  unfold RootSlice.sumProbability RootSlice.probability
  apply FiniteDist.eventMass_positive_of_atom _ _ configuration
  · change (∑ i, (configuration i : ℤ)) = -(a : ℤ)
    have hpoint (i : Fin count) : (configuration i : ℤ) =
        if i = first then -(a : ℤ) else 0 := by
      dsimp [configuration]
      split_ifs <;> rfl
    simp only [hpoint, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · change 0 < ∏ i, (windowGaussian width cutoff).weight (configuration i)
    exact Finset.prod_pos fun i _ => windowGaussian_positive width cutoff (configuration i)

def rootMarginal (width : ℝ) (cutoff population : ℕ) (hn : 0 < population) :
    FiniteDist (Window cutoff) :=
  RootSlice.marginalLaw (windowGaussian width cutoff) (fun z => (z : ℤ)) population hn
    (window_root_probability_positive width cutoff population)

theorem rootMarginal_positive (width : ℝ) (cutoff population : ℕ)
    (hn : 2 ≤ population) (a : Window cutoff) :
    0 < (rootMarginal width cutoff population (by omega)).weight a := by
  unfold rootMarginal
  rw [RootSlice.marginalLaw_weight]
  exact div_pos (mul_pos (windowGaussian_positive _ _ _)
    (window_sum_probability_positive width cutoff (population - 1) (by omega) a))
    (window_root_probability_positive width cutoff population)

def normalizedRoot (width : ℝ) {cutoff : ℕ} (a : Window cutoff) : ℝ :=
  Real.sqrt (2 * Real.pi) * (a : ℝ) / width

theorem normalizedRoot_exp_square (width : ℝ) (cutoff : ℕ) (hw : 1 ≤ width)
    (hcutoff : ⌊width⌋₊ ≤ cutoff) :
    (windowGaussian width cutoff).expectation
      (fun a => Real.exp ((1 / 4 : ℝ) * normalizedRoot width a ^ 2)) ≤
        (1 + 2 / Real.pi) * Real.sqrt 2 * Real.exp Real.pi := by
  have heq (a : Window cutoff) : (1 / 4 : ℝ) * normalizedRoot width a ^ 2 =
      Real.pi / 2 * ((a : ℝ) / width) ^ 2 := by
    unfold normalizedRoot
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    ring
  simp_rw [heq]
  exact windowGaussian_exp_square_bound width cutoff hw hcutoff

/-- Transfer to the exact marginal. The ratio comparison, when used for
the V7 family, is supplied by the proved convolution estimates. -/
theorem rootMarginal_exp_square (width comparison : ℝ) (cutoff population : ℕ)
    (hn : 0 < population) (hw : 1 ≤ width) (hcutoff : ⌊width⌋₊ ≤ cutoff)
    (hc : 0 ≤ comparison)
    (hcompare : ∀ a, (rootMarginal width cutoff population hn).weight a ≤
      comparison * (windowGaussian width cutoff).weight a) :
    (rootMarginal width cutoff population hn).expectation
      (fun a => Real.exp ((1 / 4 : ℝ) * normalizedRoot width a ^ 2)) ≤
        comparison * ((1 + 2 / Real.pi) * Real.sqrt 2 * Real.exp Real.pi) := by
  calc
    _ ≤ comparison * (windowGaussian width cutoff).expectation
        (fun a => Real.exp ((1 / 4 : ℝ) * normalizedRoot width a ^ 2)) := by
      unfold FiniteDist.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hcompare a) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalizedRoot_exp_square width cutoff hw hcutoff) hc

end

end AFT.GaussianSource

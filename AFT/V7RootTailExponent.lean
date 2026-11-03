import AFT.ActualRootBudget
import AFT.RootProbabilityParameters

/-! # The actual conditioning and queue cost is uniformly bounded -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

/-- The exact root probability and the true Hilbert budgets make the entire
conditional Fock exponent at most one, with no analytic premise remaining. -/
theorem actual_root_tail_exponent_eventually :
    ∀ᶠ parameter : ℕ in atTop,
      16 * (1184 / (parameter : ℝ) ^ 7) ^ 2 +
        (2048 * ∑ _ : Fin (Parameters.bodies parameter), (296 / (parameter : ℝ) ^ 47) ^ 2) *
          Real.log (2 * Real.exp 1 /
            rootProbability (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter) 0) ≤ 1 := by
  let constant : ℝ := 2048 * 175232 * 16 * Real.exp 3
  have hsmall1 := ((tendsto_const_div_pow (22429696 : ℝ) 14 (by decide)).comp
    tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hsmall2 := ((tendsto_const_div_pow constant 3 (by decide)).comp
    tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [v7_rootProbability_order, hsmall1, hsmall2, eventually_ge_atTop 1000000000]
    with parameter hp hsmall1 hsmall2 hlarge
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  let probability := rootProbability (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter) 0
  let budget := ∑ _ : Fin (Parameters.bodies parameter), (296 / (parameter : ℝ) ^ 47) ^ 2
  have hprob : 0 < probability :=
    (show 0 < 1 / (8 * Real.exp 2 * (parameter : ℝ) ^ 31) by positivity).trans_le hp.1
  have hlog : Real.log (2 * Real.exp 1 / probability) ≤ 16 * Real.exp 3 * (parameter : ℝ) ^ 31 := by
    calc
      _ ≤ 2 * Real.exp 1 / probability := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      _ ≤ 2 * Real.exp 1 / (1 / (8 * Real.exp 2 * (parameter : ℝ) ^ 31)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hp.1
      _ = _ := by
        rw [one_div, div_inv_eq_mul]
        have he : Real.exp 1 * Real.exp 2 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
        calc
          _ = 16 * (Real.exp 1 * Real.exp 2) * (parameter : ℝ) ^ 31 := by ring
          _ = _ := by rw [he]
  have hb := actual_root_budget parameter hlarge
  have hfirst : 16 * (1184 / (parameter : ℝ) ^ 7) ^ 2 ≤ 1 / 2 := by
    have heq : 16 * (1184 / (parameter : ℝ) ^ 7) ^ 2 = 22429696 / (parameter : ℝ) ^ 14 := by field_simp; ring
    rw [heq]
    exact hsmall1.le
  have hsecond : (2048 * budget) * Real.log (2 * Real.exp 1 / probability) ≤ 1 / 2 := by
    calc
      _ ≤ (2048 * budget) * (16 * Real.exp 3 * (parameter : ℝ) ^ 31) :=
        mul_le_mul_of_nonneg_left hlog (by dsimp only [budget]; positivity)
      _ ≤ (2048 * (175232 / (parameter : ℝ) ^ 34)) * (16 * Real.exp 3 * (parameter : ℝ) ^ 31) := by
        gcongr
        exact hb.2.1
      _ = constant / (parameter : ℝ) ^ 3 := by dsimp only [constant]; field_simp
      _ ≤ 1 / 2 := hsmall2.le
  exact (add_le_add hfirst hsecond).trans (by norm_num)

end

end AFT.V7Calibration

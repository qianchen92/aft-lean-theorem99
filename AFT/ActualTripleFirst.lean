import AFT.ActualTripleEnergy
import AFT.ActualPairMarginals
import AFT.TripleMarginals

/-! # The sharp first coefficient of the genuine fixed-root triple -/

namespace AFT.V7Calibration

open Filter GaussianSource PhysicalBlockTensors
open scoped BigOperators Classical Topology

noncomputable section

local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The actual linear coefficient has the much smaller `λ²²` square scale;
using the entire triple density here would incorrectly lose eight powers. -/
theorem actual_fixed_root_triple_first_power_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root queue : ℤ,
      |root| ≤ (v7RootCutoff parameter : ℤ) → |queue| ≤ (queueCutoff parameter : ℤ) →
      BlockFock.tensorEnergy (LocalTensors.degreeTensor
        (fun _ : Fin 3 => actualReferenceLaw cutoffScale parameter (beta parameter))
        (actualFixedRootTripleLaw cutoffScale parameter (beta parameter) root queue).weight 1) ≤
          100000 * (parameter : ℝ) ^ 22 := by
  filter_upwards [actual_pair_branch_mixture_eventually cutoffScale hscale beta hbeta,
    actual_pair_marginal_bounds_eventually cutoffScale hscale beta hbeta,
    actual_shifted_body_law_eventually cutoffScale hscale beta hbeta,
    actual_marked_primary_square_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hpair hmargin hbody hmarked hprimary hlaws href hlarge root queue hroot hqueue
  let reference := actualReferenceLaw cutoffScale parameter (beta parameter)
  let law := actualFixedRootTripleLaw cutoffScale parameter (beta parameter) root queue
  let marginal (slot : Fin 3) := law.map (fun word => word slot)
  let primary := actualPrimary cutoffScale parameter (beta parameter)
  let a := v7Activation cutoffScale parameter
  let q : ℝ := Parameters.modulus parameter
  let x : ℝ := parameter
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hx : 0 < x := by dsimp only [x]; exact_mod_cast (by omega : 0 < parameter)
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast (by omega : 1 ≤ parameter)
  have hx22 : 1 ≤ x ^ 22 := one_le_pow₀ hx1
  have hqBound : q ≤ 2 * x ^ 40 := by
    dsimp only [q, x]
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hlarge] using (Parameters.modulus_bounds parameter).2)
  have hwidth : (Parameters.anchorWidth parameter : ℝ) = x ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hlarge, Nat.cast_pow, x]
  have ha0 : 0 ≤ a := by
    dsimp only [a, v7Activation, GaussianSource.activation]
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have hr (color) : 1 / (2 * q) ≤ reference.weight color := by
    dsimp only [reference]
    rw [hlaws.2.2]
    exact href color
  have hrpos (color) : 0 < reference.weight color := (by positivity : 0 < 1 / (2 * q)).trans_le (hr color)
  have hm0 (color) : (marginal 0).weight color ≤ a * primary color + 2 / q := by
    dsimp only [marginal, law, actualFixedRootTripleLaw]
    rw [sharedSourceTriple_first_marginal]
    simp only [hpair]
    exact (hmargin color).1
  have hm1 (color) : (marginal 1).weight color ≤ 1 / (Parameters.anchorWidth parameter : ℝ) + 2 / q := by
    dsimp only [marginal, law, actualFixedRootTripleLaw]
    rw [sharedSourceTriple_second_marginal]
    simp only [hpair]
    exact (hmargin color).2
  have hm2 (color) : (marginal 2).weight color ≤ 4 / q := by
    apply sharedSourceTriple_body_marginal_le
      (actualActivatedSource cutoffScale parameter) (actualPairBranch cutoffScale parameter (beta parameter))
      (actualBodyBranch cutoffScale parameter (beta parameter) root queue) (4 / q) _ color
    intro sample first second attached
    exact (hbody _ (actualBodyBranch_shift_bound cutoffScale parameter root queue hroot hqueue sample)).2 attached
  have he0 : profileSquareNorm reference.weight (marginal 0).weight ≤ 6168 * x ^ 22 := by
    have hh := probability_energy_le_primary_square reference (marginal 0) primary a (2 / q) (1 / (2 * q))
      ha0 (by positivity) (by positivity) (fun color => (hprimary.1 color).le) hr hm0
    simp only [Fintype.card_fin] at hh
    have heq : (2 / (1 / (2 * q))) * (a ^ 2 * (∑ color, primary color ^ 2) +
        (Parameters.modulus parameter : ℝ) * (2 / q) ^ 2) =
        4 * q * (a ^ 2 * ∑ color, primary color ^ 2) + 16 := by
      change (2 / (1 / (2 * q))) * (a ^ 2 * (∑ color, primary color ^ 2) + q * (2 / q) ^ 2) = _
      field_simp
      ring
    rw [heq] at hh
    calc
      _ ≤ 4 * q * (a ^ 2 * ∑ color, primary color ^ 2) + 16 := hh
      _ ≤ 4 * (2 * x ^ 40) * (769 / x ^ 18) + 16 := by
        gcongr
      _ = 6152 * x ^ 22 + 16 := by field_simp; ring
      _ ≤ _ := by nlinarith only [hx22]
  have he1 : profileSquareNorm reference.weight (marginal 1).weight ≤ 8 * x ^ 22 := by
    have hh := probability_energy_le_height reference (marginal 1) (1 / (2 * q))
      (1 / (Parameters.anchorWidth parameter : ℝ) + 2 / q) (by positivity) (by positivity) hr hm1
    rw [hwidth] at hh
    have heq : (1 / x ^ 32 + 2 / q) / (1 / (2 * q)) = 2 * q / x ^ 32 + 4 := by field_simp; ring
    rw [heq] at hh
    have hpower : x ^ 8 ≤ x ^ 22 := pow_le_pow_right₀ hx1 (by norm_num)
    calc
      _ ≤ 2 * q / x ^ 32 + 4 := hh
      _ ≤ 2 * (2 * x ^ 40) / x ^ 32 + 4 := by gcongr
      _ = 4 * x ^ 8 + 4 := by field_simp; ring
      _ ≤ _ := by linarith
  have he2 : profileSquareNorm reference.weight (marginal 2).weight ≤ 8 := by
    have hh := probability_energy_le_height reference (marginal 2) (1 / (2 * q)) (4 / q)
      (by positivity) (by positivity) hr hm2
    exact hh.trans_eq (by field_simp; ring)
  have hc0 := centered_probability_energy_le reference (marginal 0) hrpos
  have hc1 := centered_probability_energy_le reference (marginal 1) hrpos
  have hc2 := centered_probability_energy_le reference (marginal 2) hrpos
  have hsum : (∑ slot : Fin 3, profileSquareNorm reference.weight
      (fun color => (marginal slot).weight color - reference.weight color)) ≤ 12374 * x ^ 22 := by
    rw [Fin.sum_univ_three]
    linarith
  have hh := LocalTensors.first_degree_energy_le (fun _ : Fin 3 => reference) (fun _ => hrpos) law
  simp only [Fintype.card_fin] at hh
  calc
    _ ≤ 8 * ∑ slot : Fin 3, profileSquareNorm reference.weight
        (fun color => (marginal slot).weight color - reference.weight color) := by simpa only [marginal, show (2 : ℝ) ^ 3 = 8 by norm_num] using hh
    _ ≤ 8 * (12374 * x ^ 22) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ _ := by change _ ≤ 100000 * x ^ 22; nlinarith [pow_nonneg hx.le 22]

end

end AFT.V7Calibration

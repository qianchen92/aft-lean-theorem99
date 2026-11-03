import AFT.ActualPairedBudgets
import AFT.PrimaryLawLower

/-! # Actual fixed-root anchor differences in the primary metric -/
namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

def integerAnchorDifferenceProfile (parameter : ℕ) (shift : ℤ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) : Fin (Parameters.modulus parameter) → ℝ :=
  integerAnchorShiftProfile parameter shift profile - integerAnchorShiftProfile parameter 0 profile

theorem integerAnchorDifferenceProfile_eq (parameter : ℕ) (shift : ℤ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    integerAnchorDifferenceProfile parameter shift profile output =
      ((∑ input, intervalAnchorDifference (fun color => publicAnchorStart (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color true) shift (Parameters.anchorWidth parameter) input output.val * profile input) +
       (∑ input, intervalAnchorDifference (fun color => publicAnchorStart (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color false) shift (Parameters.anchorWidth parameter) input output.val * profile input)) / 2 := by
  simp only [integerAnchorDifferenceProfile, Pi.sub_apply, integerAnchorShiftProfile,
    integerAnchorProfile, publicAnchorKernel, sub_zero, intervalAnchorDifference,
    intervalAnchorLaw_translate, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro input _
  ring

theorem integerAnchorDifferenceProfile_energy (parameter : ℕ) (shift : ℤ)
    (primary profile : Fin (Parameters.modulus parameter) → ℝ) (lower : ℝ)
    (hp : ∀ color, 0 < primary color) (hmass : ∑ color, primary color = 1)
    (hlower : 0 < lower) (hout : ∀ color, lower ≤ primary color) :
    profileSquareNorm primary (integerAnchorDifferenceProfile parameter shift profile) ≤
      (2 * (shift.natAbs : ℝ) / ((Parameters.anchorWidth parameter : ℝ) ^ 2 * lower)) *
        profileSquareNorm primary profile := by
  let part (coin : Bool) (output : Fin (Parameters.modulus parameter)) :=
    ∑ input, intervalAnchorDifference (fun color => publicAnchorStart (Parameters.modulus parameter)
      (Parameters.anchorWidth parameter) color coin) shift (Parameters.anchorWidth parameter) input output.val * profile input
  have hb (coin : Bool) := finitePalette_anchorProfile_bound
    (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ))
    (fun color => publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color coin)
    (by intro first second he; change (first.val : ℤ) = second.val at he; apply Fin.ext; exact_mod_cast he)
    shift (Parameters.anchorWidth parameter) primary profile lower hp hmass hlower hout
  have hconv : profileSquareNorm primary (integerAnchorDifferenceProfile parameter shift profile) ≤
      (profileSquareNorm primary (part true) + profileSquareNorm primary (part false)) / 2 := by
    unfold profileSquareNorm
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro output _
    rw [integerAnchorDifferenceProfile_eq]
    change ((part true output + part false output) / 2) ^ 2 / primary output ≤ _
    have hs : ((part true output + part false output) / 2) ^ 2 ≤
        ((part true output) ^ 2 + (part false output) ^ 2) / 2 := by
      nlinarith [sq_nonneg (part true output - part false output)]
    apply (div_le_div_of_nonneg_right hs (hp output).le).trans_eq
    ring
  linarith [hb true, hb false]

theorem integerAnchorDifferenceProfile_row (parameter : ℕ) (shift : ℤ)
    (primary profile : Fin (Parameters.modulus parameter) → ℝ) (lower : ℝ)
    (hp : ∀ color, 0 < primary color) (hmass : ∑ color, primary color = 1)
    (hlower : 0 < lower) (hout : ∀ color, lower ≤ primary color)
    (output : Fin (Parameters.modulus parameter)) :
    |integerAnchorDifferenceProfile parameter shift profile output / primary output| ≤
      (1 / ((Parameters.anchorWidth parameter : ℝ) * lower)) * Real.sqrt (profileSquareNorm primary profile) := by
  let part (coin : Bool) :=
    ∑ input, intervalAnchorDifference (fun color => publicAnchorStart (Parameters.modulus parameter)
      (Parameters.anchorWidth parameter) color coin) shift (Parameters.anchorWidth parameter) input output.val * profile input
  have hb (coin : Bool) := intervalAnchorDifference_density_row_bound
    (fun color => publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color coin)
    shift output.val (Parameters.anchorWidth parameter) primary profile (primary output) lower hp hmass hlower (hout output)
  rw [integerAnchorDifferenceProfile_eq]
  change |((part true + part false) / 2) / primary output| ≤ _
  have he : ((part true + part false) / 2) / primary output =
      (part true / primary output + part false / primary output) / 2 := by ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ht := abs_add_le (part true / primary output) (part false / primary output)
  linarith [hb true, hb false]

/-- The physical interval width and actual primary lower bound give the
root-anchor square scale `λ⁻²²` and all fixed output rows cost `λ⁸`. -/
theorem actual_root_anchor_difference_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ shift : ℤ, |shift| ≤ (v7RootCutoff parameter : ℤ) →
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ,
      profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight
        (integerAnchorDifferenceProfile parameter shift profile) ≤
          (48 / (parameter : ℝ) ^ 22) * profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile ∧
      ∀ output, |integerAnchorDifferenceProfile parameter shift profile output /
        (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight output| ≤
          8 * (parameter : ℝ) ^ 8 * Real.sqrt (profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile) := by
  filter_upwards [actual_primary_law_quarter_lower_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hl hp2 shift hshift profile
  let p := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let q : ℝ := Parameters.modulus parameter
  let x : ℝ := parameter
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < parameter)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hp (color) : 0 < p.weight color := (by positivity : 0 < 1 / (4 * q)).trans_le (hl color)
  have hw : (Parameters.anchorWidth parameter : ℝ) = x ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp2, Nat.cast_pow, x]
  have hqw : q ≤ 2 * x ^ 40 := by
    dsimp only [q, x]
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hp2] using (Parameters.modulus_bounds parameter).2)
  have hs : (shift.natAbs : ℝ) ≤ 3 * x ^ 2 := by
    have hs' : (shift.natAbs : ℤ) ≤ 3 * (parameter : ℤ) ^ 2 := by
      rw [Int.natCast_natAbs]
      have hb : v7RootCutoff parameter ≤ 3 * parameter ^ 2 := Nat.sub_le _ _
      exact hshift.trans (by exact_mod_cast hb)
    dsimp only [x]
    exact_mod_cast hs'
  have henergy := integerAnchorDifferenceProfile_energy parameter shift p.weight profile (1 / (4 * q)) hp p.sum_one (by positivity) hl
  have hn := profileSquareNorm_nonneg p.weight profile (fun color => p.nonneg color)
  have hc : 2 * (shift.natAbs : ℝ) / ((Parameters.anchorWidth parameter : ℝ) ^ 2 * (1 / (4 * q))) ≤ 48 / x ^ 22 := by
    rw [hw]
    calc
      _ = 8 * q * (shift.natAbs : ℝ) / x ^ 64 := by field_simp; ring
      _ ≤ 8 * (2 * x ^ 40) * (3 * x ^ 2) / x ^ 64 := by gcongr
      _ = _ := by field_simp; ring
  refine ⟨henergy.trans (mul_le_mul_of_nonneg_right hc hn), ?_⟩
  intro output
  apply (integerAnchorDifferenceProfile_row parameter shift p.weight profile (1 / (4 * q)) hp p.sum_one (by positivity) hl output).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [hw]
  calc
    _ = 4 * q / x ^ 32 := by field_simp
    _ ≤ 4 * (2 * x ^ 40) / x ^ 32 := by gcongr
    _ = _ := by field_simp; ring

end
end AFT.V7Calibration

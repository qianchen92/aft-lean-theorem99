import AFT.PairInputFibers
import AFT.PairDifferenceReference
import AFT.MixedPair

/-! # From literal signed pair masses to all four density fibers -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G]

/-- The full density norm uses the complete signed mass energy, separately
from the fixed-coordinate estimates. -/
theorem pair_density_energy_le (mass : G × G → ℝ) (reference : G → ℝ)
    (lower full : ℝ) (hl : 0 < lower) (href : ∀ x, lower ≤ reference x)
    (hfull : countingL2 mass ≤ full) :
    (∑ x, ∑ y, reference x * reference y * (mass (x,y) / (reference x * reference y)) ^ 2) ≤
      full ^ 2 / lower ^ 2 := by
  have hp (x : G) : 0 < reference x := hl.trans_le (href x)
  have hmass : (∑ x, ∑ y, mass (x,y)^2) ≤ full ^ 2 := by
    have hh := pow_le_pow_left₀ (countingL2_nonneg mass) hfull 2
    unfold countingL2 at hh
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hh
    simpa only [Fintype.sum_prod_type] using hh
  calc
    _ = ∑ x, ∑ y, mass (x,y)^2 / (reference x * reference y) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      field_simp
    _ ≤ ∑ x, ∑ y, mass (x,y)^2 / lower ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hl)
      simpa only [pow_two] using mul_le_mul (href x) (href y) hl.le (hp x).le
    _ = (∑ x, ∑ y, mass (x,y)^2) / lower ^ 2 := by simp only [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right hmass (sq_nonneg _)

theorem RowBound.density_fiber {bound : ℝ} {mass : G × G → ℝ}
    (h : RowBound bound mass) (reference : G → ℝ) (lower : ℝ)
    (hl : 0 < lower) (href : ∀ x, lower ≤ reference x) (x : G) :
    (∑ y, reference y * (mass (x,y) / (reference x * reference y)) ^ 2) ≤
      bound ^ 2 / lower ^ 3 := by
  apply (TrimmedSlice.pairDifference_density_bounds (fun x y => mass (x,y)) reference lower (bound ^ 2)
    hl href (fun x => ?_)).2 x
  have hh := pow_le_pow_left₀ (countingL2_nonneg _) (h x) 2
  simpa only [countingL2, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] using hh

/-- All four fibers are controlled by the actual full energy, both actual
fixed-coordinate row norms, and the actual pointwise mass bound. -/
theorem pair_mass_activity_le (mass : G × G → ℝ) (reference : FiniteDist G)
    (lower full row column height rate : ℝ) (hl : 0 < lower)
    (href : ∀ x, lower ≤ reference.weight x) (hrate : 0 ≤ rate)
    (hfull : countingL2 mass ≤ full) (hrow : RowBound row mass)
    (hcolumn : RowBound column (fun point => mass point.swap))
    (hheight : SupBound height mass) (hheight0 : 0 ≤ height) :
    MixedKernel.activity ![rate,rate] (MixedKernel.pairReference reference reference)
      (MixedKernel.pairKernel (fun x y => mass (x,y) / (reference.weight x * reference.weight y))) ≤
      rate ^ 2 * (Real.sqrt (full ^ 2 / lower ^ 2) +
        rate * Real.sqrt (row ^ 2 / lower ^ 3) + rate * Real.sqrt (column ^ 2 / lower ^ 3) +
        rate ^ 2 * (height / lower ^ 2)) := by
  have hh := MixedKernel.pair_activity_le reference reference
    (fun x y => mass (x,y) / (reference.weight x * reference.weight y)) rate rate
    (Real.sqrt (full ^ 2 / lower ^ 2)) (Real.sqrt (row ^ 2 / lower ^ 3))
    (Real.sqrt (column ^ 2 / lower ^ 3)) (height / lower ^ 2)
    hrate hrate (by positivity) (by positivity) (by positivity) (by positivity)
    (by rw [Real.sq_sqrt (by positivity)]; exact pair_density_energy_le mass reference.weight lower full hl href hfull)
    (by intro x; rw [Real.sq_sqrt (by positivity)]; exact hrow.density_fiber reference.weight lower hl href x)
    (by intro y; rw [Real.sq_sqrt (by positivity)];
        simpa only [mul_comm] using hcolumn.density_fiber reference.weight lower hl href y)
    (fun x y => TrimmedSlice.pairDifference_density_sup (fun x y => mass (x,y)) reference.weight lower height
      hl hheight0 href (fun x y => hheight (x,y)) x y)
  simpa only [pow_two] using hh

end AFT.SafeConvolution

import AFT.ReferenceProbability

/-! # Actual reference-to-primary density comparison in every fiber -/

namespace AFT.V7Calibration
open Filter GaussianSource
open scoped BigOperators Classical Topology
noncomputable section

theorem actual_reference_primary_density_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      let p := actualPrimary cutoffScale parameter (beta parameter)
      let r := actualReferenceMean cutoffScale parameter (beta parameter)
      (∀ color, |r color / p color| ≤ 8) ∧
      (∑ color, p color * (r color / p color)^2) ≤ 8 := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [actual_reference_probability_eventually cutoffScale hscale beta hbeta,
    primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
      (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
      (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel] with parameter hr hp
  dsimp only at hp ⊢
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hp0 (color) : 0 < p color := lt_of_lt_of_le (by positivity) (hp.1 color)
  have hR (color) : |r color / p color| ≤ 8 := by
    have hh := mul_le_mul_of_nonneg_left (hp.1 color) (by norm_num : (0 : ℝ) ≤ 8)
    have hh' : 2 / (Parameters.modulus parameter : ℝ) ≤ 8 * p color := by convert hh using 1; ring
    rw [abs_of_nonneg (div_nonneg (hr.1 color).1 (hp0 color).le)]
    exact (div_le_iff₀ (hp0 color)).mpr ((hr.1 color).2.trans hh')
  refine ⟨hR, ?_⟩
  change (∑ color, p color*(r color/p color)^2) ≤ _
  calc
    _ ≤ ∑ color, 8*r color := by
      apply Finset.sum_le_sum
      intro color _
      have hh := mul_le_mul_of_nonneg_right (hR color) (hr.1 color).1
      rw [abs_of_nonneg (div_nonneg (hr.1 color).1 (hp0 color).le)] at hh
      change (r color / p color) * r color ≤ 8*r color at hh
      convert hh using 1
      field_simp [ne_of_gt (hp0 color)]
    _ = _ := by rw [← Finset.mul_sum, hr.2]; norm_num

end
end AFT.V7Calibration

import AFT.V7ReferenceLaws

/-! # The actual calibrated primary law has the proved pointwise lower bound -/

namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section

theorem actual_primary_law_quarter_lower_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color,
      1 / (4 * (Parameters.modulus parameter : ℝ)) ≤
        (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta] with parameter hp hl color
  rw [hl.1]
  exact hp.1 color

end
end AFT.V7Calibration

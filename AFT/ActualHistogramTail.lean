import AFT.ActualMixedTail

/-! # The complete actual signed tails on literal histogram space -/

namespace AFT.HistogramNormalization
open scoped BigOperators Classical
noncomputable section
/-- The exact multinomial-reference norm of a function on histograms. -/
def histogramReferenceEnergy {Color : Type*} [Fintype Color] (reference : FiniteDist Color)
    (population : ℕ) (value : Histogram population Color → ℝ) : ℝ :=
  ((FiniteDist.independent (fun _ : Fin population => reference)).map histogram).l2Sq value
end
end AFT.HistogramNormalization

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
local instance actualHistogramTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualHistogramTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- The complete unweighted tail is an actual function on histograms under
the multinomial reference, with exactly the same norm as its labeled lift. -/
theorem actual_histogram_tail_exists (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ cutoff : ℕ,
      ∃ tail : Histogram (Fintype.card (Sigma (blockSlots parameter))) (Fin (Parameters.modulus parameter)) → ℝ,
        densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (renamedMass (Fintype.equivFin (Sigma (blockSlots parameter)))
            (actualRootQueueMass cutoffScale parameter (beta parameter)))) cutoff = tail ∘ histogram ∧
        histogramReferenceEnergy (actualReferenceLaw cutoffScale parameter (beta parameter))
          (Fintype.card (Sigma (blockSlots parameter))) tail ≤
          (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) * (16 * Real.exp 1) := by
  filter_upwards [actual_complete_histogram_tail cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta] with parameter ht hl hr cutoff
  have href (color) : 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.2.2]
    have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
    exact (by positivity : 0 < 1 / (2 * (Parameters.modulus parameter : ℝ))).trans_le (hr color)
  obtain ⟨tail, hid, he⟩ := actual_signed_renamed_histogram_tail
    (actualReferenceLaw cutoffScale parameter (beta parameter)) href
    (actualRootQueueMass cutoffScale parameter (beta parameter)) cutoff
  exact ⟨tail, hid, he.le.trans (ht cutoff)⟩

/-- Arbitrary jointly marked signed outputs also have their complete
all-degree tails on actual histogram space, with no positivity assumption. -/
theorem actual_mixed_histogram_tail_exists (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ selected : Finset (blockIndex parameter),
      ∀ tagged : ActualTaggedOutput parameter selected, ∀ cutoff : ℕ,
      ∃ tail : Histogram (Fintype.card (actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected))
          (Fin (Parameters.modulus parameter)) → ℝ,
        densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (renamedMass (Fintype.equivFin (actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected))
            (actualMarkedRootQueueMass cutoffScale parameter (beta parameter) selected tagged))) cutoff = tail ∘ histogram ∧
        histogramReferenceEnergy (actualReferenceLaw cutoffScale parameter (beta parameter))
          (Fintype.card (actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected)) tail ≤
          (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) *
            (actualTaggedEnergyBudget cutoffScale parameter (beta parameter) selected tagged *
              (16 * Real.exp (1 + 16 * (1 + (selected.card : ℝ)) ^ 2))) := by
  filter_upwards [actual_complete_mixed_histogram_tail cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta] with parameter ht hl hr selected tagged cutoff
  have href (color) : 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.2.2]
    have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
    exact (by positivity : 0 < 1 / (2 * (Parameters.modulus parameter : ℝ))).trans_le (hr color)
  obtain ⟨tail, hid, he⟩ := actual_signed_renamed_histogram_tail
    (actualReferenceLaw cutoffScale parameter (beta parameter)) href
    (actualMarkedRootQueueMass cutoffScale parameter (beta parameter) selected tagged) cutoff
  exact ⟨tail, hid, he.le.trans (ht selected tagged cutoff)⟩

end
end AFT.V7Calibration

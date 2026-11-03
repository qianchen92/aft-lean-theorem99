import AFT.ActualInputMixedTail
import AFT.ActualHistogramTail

/-! # The actual full histogram tail of arbitrary joint canonical input -/
namespace AFT.V7Calibration
open Filter GaussianSource HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
local instance actualInputHistogramTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualInputHistogramTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- The input-to-output bound is on the actual multinomial histogram space
and includes every output degree, with the same original pool-rate factors. -/
theorem actual_input_histogram_tail_exists (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
        conditionalJointOutput cutoffScale parameter mark attached first second) ∧
      ∀ count : ℕ, ∀ role : Fin count → Bool, ∀ selected : Finset (blockIndex parameter),
      ∀ placement : ActualTaggedPlacement parameter count role selected,
      ∀ kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ,
      Hoeffding.Canonical (fun index => actualRoleInput cutoffScale parameter (beta parameter) (role index)) Finset.univ kernel →
      ∀ cutoff : ℕ,
      ∃ tail : Histogram (Fintype.card (actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected))
          (Fin (Parameters.modulus parameter)) → ℝ,
        densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (renamedMass (Fintype.equivFin (actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected))
            (actualMarkedRootQueueMass cutoffScale parameter (beta parameter) selected
              (actualJointTaggedOutput cutoffScale parameter (beta parameter) charts count role selected placement kernel)))) cutoff =
          tail ∘ histogram ∧
        histogramReferenceEnergy (actualReferenceLaw cutoffScale parameter (beta parameter))
          (Fintype.card (actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected)) tail ≤
          (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) *
            (actualJointInputEnergy cutoffScale parameter (beta parameter) count role kernel *
              (16 * Real.exp (1 + 16 * (1 + (selected.card : ℝ)) ^ 2))) := by
  filter_upwards [actual_input_complete_mixed_tail cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta] with parameter ht hl hr
  obtain ⟨charts, hcharts, htail⟩ := ht
  refine ⟨charts, hcharts, ?_⟩
  intro count role selected placement kernel hcanonical cutoff
  have href (color) : 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.2.2]
    have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
    exact (by positivity : 0 < 1 / (2 * (Parameters.modulus parameter : ℝ))).trans_le (hr color)
  obtain ⟨tail, hid, he⟩ := actual_signed_renamed_histogram_tail
    (actualReferenceLaw cutoffScale parameter (beta parameter)) href
    (actualMarkedRootQueueMass cutoffScale parameter (beta parameter) selected
      (actualJointTaggedOutput cutoffScale parameter (beta parameter) charts count role selected placement kernel)) cutoff
  exact ⟨tail, hid, he.le.trans (htail count role selected placement kernel hcanonical cutoff)⟩

end
end AFT.V7Calibration

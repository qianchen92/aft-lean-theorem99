import AFT.ActualInputHistogramTail
import AFT.ReindexedTailEnergy
import AFT.SignedTailSum

/-! # Actual controlled tails on the common full physical output space -/
namespace AFT.V7Calibration
open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualPlacedInputTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualPlacedInputTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- The actual selected input channel and its physical complement, placed
back on the common output slots of the original construction. -/
def actualPlacedInputMass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex parameter))
    (placement : ActualTaggedPlacement parameter count role selected)
    (kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ) :
    (Sigma (blockSlots parameter) → Fin (Parameters.modulus parameter)) → ℝ :=
  renamedMass (splitSlotsEquiv (blockSlots parameter) selected)
    (actualMarkedRootQueueMass cutoffScale parameter beta selected
      (actualJointTaggedOutput cutoffScale parameter beta charts count role selected placement kernel))

/-- Distinct marked supports produce actual signed laws on one common
space. Their complete tail bounds therefore combine by the true L2 triangle
inequality without an artificial factor for the number of representations. -/
theorem actual_placed_input_tail_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
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
      (FiniteDist.independent (fun _ : Sigma (blockSlots parameter) => actualReferenceLaw cutoffScale parameter (beta parameter))).l2Sq
        (densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (actualPlacedInputMass cutoffScale parameter (beta parameter) charts count role selected placement kernel)) cutoff) ≤
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
  unfold actualPlacedInputMass
  rw [symmetrized_renamed_tail_energy _ _ href]
  exact htail count role selected placement kernel hcanonical cutoff

end
end AFT.V7Calibration

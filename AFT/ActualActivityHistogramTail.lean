import AFT.ActualInputHistogramTail
import AFT.ActualFockPoolRates

/-! # The complete actual histogram tail in the full mixed input activity -/
namespace AFT.V7Calibration
open Filter GaussianSource HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualActivityHistogramTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualActivityHistogramTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

def actualJointActivityEnergy (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (count : ℕ) (role : Fin count → Bool) (pool : Fin count → ℕ)
    (kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ) : ℝ :=
  letI : DecidableEq (Fin count) := Classical.decEq _
  ((Fintype.card (Sigma (fun index => actualRoleSlots (role index))) + 1 : ℕ) * (5 ^ count : ℕ) *
    ((count * 4).factorial : ℝ)) *
      ((∏ index, actualRoleRateFactor parameter (role index) ^ 2) *
        MixedKernel.activity (fun index => 1 / Real.sqrt (pool index))
          (fun index => actualRoleInput cutoffScale parameter beta (role index)) kernel ^ 2)

/-- Both full retained-pool powers are preserved in the actual mixed
activity; each body coordinate incurs only its stated radius factor. -/
theorem actualJointInputEnergy_le_activity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hp : 2 ≤ parameter) (count : ℕ) (role : Fin count → Bool) (pool : Fin count → ℕ)
    (hpool : ∀ index, 0 < pool index)
    (hcapacity : ∀ index, pool index ≤ actualRolePoolCapacity parameter (role index))
    (kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ) :
    actualJointInputEnergy cutoffScale parameter beta count role kernel ≤
      actualJointActivityEnergy cutoffScale parameter beta count role pool kernel := by
  letI : DecidableEq (Fin count) := Classical.decEq _
  have h := actual_role_product_energy_le_activity cutoffScale parameter beta hp count role pool hpool hcapacity kernel
  unfold actualJointInputEnergy actualJointActivityEnergy
  exact mul_le_mul_of_nonneg_left
    h
    (by positivity)

/-- A single full mixed-control histogram-tail theorem: the input is the
actual canonical joint kernel and full mixed activity on genuine retained
pools, the output is the actual root-conditioned common-queue signed law,
and all local physical estimates and all output degrees have been proved. -/
theorem actual_activity_histogram_tail_exists (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
        conditionalJointOutput cutoffScale parameter mark attached first second) ∧
      ∀ count : ℕ, ∀ role : Fin count → Bool, ∀ selected : Finset (blockIndex parameter),
      ∀ placement : ActualTaggedPlacement parameter count role selected, ∀ pool : Fin count → ℕ,
      (∀ index, 0 < pool index) →
      (∀ index, pool index ≤ actualRolePoolCapacity parameter (role index)) →
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
            (actualJointActivityEnergy cutoffScale parameter (beta parameter) count role pool kernel *
              (16 * Real.exp (1 + 16 * (1 + (selected.card : ℝ)) ^ 2))) := by
  filter_upwards [actual_input_histogram_tail_exists cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter ht hp
  obtain ⟨charts, hcharts, htail⟩ := ht
  refine ⟨charts, hcharts, ?_⟩
  intro count role selected placement pool hpool hcapacity kernel hcanonical cutoff
  obtain ⟨tail, hid, he⟩ := htail count role selected placement kernel hcanonical cutoff
  refine ⟨tail, hid, he.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (actualJointInputEnergy_le_activity cutoffScale parameter (beta parameter) hp count role pool hpool hcapacity kernel)
      (by positivity)) (by positivity)

end
end AFT.V7Calibration

import AFT.ActualJointFock
import AFT.ActualMixedTail

/-! # The complete mixed tail of actual arbitrary joint primary/body input -/
namespace AFT.V7Calibration
open Filter GaussianSource LocalTensors JointPhysicalChannel HistogramNormalization BlockProducts
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualInputMixedTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualInputMixedTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualInputMixedTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Physical slot placement together with the actual source coordinates used
by its primary, attached, compensator and singleton channels. -/
structure ActualTaggedPlacement (parameter count : ℕ) (role : Fin count → Bool)
    (selected : Finset (blockIndex parameter)) where
  attached : Fin count → blockIndex parameter
  compensator : Fin count → blockIndex parameter
  body : Fin count → blockIndex parameter
  slots : Sigma (fun index => actualRoleSlots (role index)) ≃ actualMarkedSlots parameter selected

/-- A placement can tag only a bounded number of original blocks: each has
at least one output, while each marked input has at most four outputs. -/
theorem ActualTaggedPlacement.selected_card_le {parameter count : ℕ} {role : Fin count → Bool}
    {selected : Finset (blockIndex parameter)} (placement : ActualTaggedPlacement parameter count role selected) :
    selected.card ≤ count * 4 := by
  have hmarked : selected.card ≤ Fintype.card (actualMarkedSlots parameter selected) := by
    rw [Fintype.card_sigma]
    calc
      _ = ∑ _ : selected, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun index _ => by
        rcases index with ⟨index, hi⟩
        cases index <;> norm_num [blockSlots]
  have hslots : Fintype.card (Sigma (fun index => actualRoleSlots (role index))) ≤ count * 4 := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _ : Fin count, 4 := Finset.sum_le_sum fun index _ => actualRoleSlots_card_le (role index)
      _ = _ := by simp
  exact hmarked.trans ((Fintype.card_congr placement.slots).symm.le.trans hslots)

/-- The true jointly signed marked mass, retaining the full common root word
and common queue sample and using the actual local physical channels. -/
def actualJointTaggedOutput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (count : ℕ) (role : Fin count → Bool) (selected : Finset (blockIndex parameter))
    (placement : ActualTaggedPlacement parameter count role selected)
    (kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ) : ActualTaggedOutput parameter selected :=
  fun word sample => renamedMass placement.slots
    (JointPhysicalChannel.mass (fun index => actualRoleSlots (role index))
      (fun index => actualRoleChannel cutoffScale parameter beta charts
        (actualRootField parameter word (placement.attached index))
        (actualRootField parameter word (placement.compensator index))
        (actualQueueShifts parameter sample (placement.attached index))
        (actualRootField parameter word (placement.body index) + actualQueueShifts parameter sample (placement.body index))
        (role index)) kernel)

/-- Explicit dimension-free input energy with the original primary and body
powers. All dependence on input order appears in its finite numerical factor. -/
def actualJointInputEnergy (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (count : ℕ) (role : Fin count → Bool)
    (kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ) : ℝ :=
  ((Fintype.card (Sigma (fun index => actualRoleSlots (role index))) + 1 : ℕ) * (5 ^ count : ℕ) *
    ((count * 4).factorial : ℝ)) *
      ((∏ index, actualRoleBound parameter (role index) ^ 2) *
        (FiniteDist.independent (fun index => actualRoleInput cutoffScale parameter beta (role index))).l2Sq kernel)

theorem actualJointInputEnergy_nonneg (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (count : ℕ) (role : Fin count → Bool)
    (kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ) :
    0 ≤ actualJointInputEnergy cutoffScale parameter beta count role kernel := by
  unfold actualJointInputEnergy
  exact mul_nonneg (by positivity) (mul_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _) (FiniteDist.l2Sq_nonneg _ _))

/-- The original complete mixed tail with every local operator/Fock estimate
proved from the actual V7 construction. No norm estimate, concentration
estimate, or inverse-response bound is left as an input assumption. -/
theorem actual_input_complete_mixed_tail (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
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
      (FiniteDist.independent (fun _ : actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected =>
        actualReferenceLaw cutoffScale parameter (beta parameter))).l2Sq
        (densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (actualMarkedRootQueueMass cutoffScale parameter (beta parameter) selected
            (actualJointTaggedOutput cutoffScale parameter (beta parameter) charts count role selected placement kernel))) cutoff) ≤
        (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) *
          (actualJointInputEnergy cutoffScale parameter (beta parameter) count role kernel *
            (16 * Real.exp (1 + 16 * (1 + (selected.card : ℝ)) ^ 2))) := by
  filter_upwards [actual_joint_fock_energy_eventually cutoffScale hscale beta hbeta,
    actual_complete_mixed_histogram_tail cutoffScale hscale beta hbeta] with parameter hj ht
  obtain ⟨charts, hcharts, hbound⟩ := hj
  refine ⟨charts, hcharts, ?_⟩
  intro count role selected placement kernel hcanonical cutoff
  let tagged := actualJointTaggedOutput cutoffScale parameter (beta parameter) charts count role selected placement kernel
  let budget := actualJointInputEnergy cutoffScale parameter (beta parameter) count role kernel
  have hb0 : 0 ≤ budget := actualJointInputEnergy_nonneg cutoffScale parameter (beta parameter) count role kernel
  have hpoint (word : actualRootWord parameter) (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :
      taggedCoefficientEnergy (actualReferenceLaw cutoffScale parameter (beta parameter)) (tagged word sample)
        (Parameters.dimension parameter) ((parameter : ℝ) ^ 2) ≤ budget := by
    dsimp only [tagged, actualJointTaggedOutput]
    rw [taggedCoefficientEnergy_renamedMass]
    apply hbound count role _ _ _ _
      (fun index => actualRootField_bound parameter word (placement.attached index))
      (fun index => actualRootField_bound parameter word (placement.compensator index))
      (fun index => actualQueueShifts_bound parameter sample (placement.attached index)) _ kernel hcanonical
    intro index
    have hh := actualBodyBranch_shift_bound cutoffScale parameter
      (actualRootField parameter word (placement.body index)) (actualQueueShifts parameter sample (placement.body index))
      (actualRootField_bound parameter word (placement.body index))
      (actualQueueShifts_bound parameter sample (placement.body index)) (Sum.inl ())
    simpa only [actualSourceShift, add_zero] using hh
  have hbudget : actualTaggedEnergyBudget cutoffScale parameter (beta parameter) selected tagged ≤ budget := by
    apply (pi_norm_le_iff_of_nonneg hb0).mpr
    intro word
    apply (pi_norm_le_iff_of_nonneg hb0).mpr
    intro sample
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint word sample
    · unfold taggedCoefficientEnergy
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun degree _ =>
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  exact (ht selected tagged cutoff).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hbudget (by positivity)) (by positivity))

end
end AFT.V7Calibration

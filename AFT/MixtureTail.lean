import AFT.PhysicalHistogramTail
import AFT.MixedTransfer

/-! # Complete signed tails commute with the actual conditioning mixture -/

namespace AFT.HistogramNormalization

open scoped BigOperators Classical

variable {Slot Color Source : Type*} [Fintype Slot] [Fintype Color] [Fintype Source]

omit [Fintype Slot] [Fintype Color] in
theorem expectation_square_le (source : FiniteDist Source) (value : Source → ℝ) :
    source.expectation value ^ 2 ≤ source.l2Sq value := by
  have h := CanonicalMoments.expectation_mul_sq_le source value (fun _ => 1)
  simpa only [mul_one, one_pow, FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.sum_one] using h

/-- The real signed mixture, including arbitrary root/queue conditioning. -/
noncomputable def mixtureMass (source : FiniteDist Source)
    (mass : Source → (Slot → Color) → ℝ) (word : Slot → Color) : ℝ :=
  source.expectation (fun sample => mass sample word)

theorem densityComponent_mixture (reference : Slot → FiniteDist Color) (source : FiniteDist Source)
    (mass : Source → (Slot → Color) → ℝ) (selected : Finset Slot) (word : Slot → Color) :
    Hoeffding.densityComponent reference (mixtureMass source mass) selected word =
      source.expectation (fun sample => Hoeffding.densityComponent reference (mass sample) selected word) := by
  unfold Hoeffding.densityComponent mixtureMass FiniteDist.expectation
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [Fintype Color] in
theorem symmetrizedMass_mixture (source : FiniteDist Source)
    (mass : Source → (Slot → Color) → ℝ) :
    symmetrizedMass (mixtureMass source mass) = mixtureMass source (fun sample => symmetrizedMass (mass sample)) := by
  funext word
  unfold symmetrizedMass BlockFock.symmetrize mixtureMass FiniteDist.expectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  apply Finset.sum_congr rfl
  intro permutation _
  ring

theorem densityTail_mixture (reference : FiniteDist Color) (source : FiniteDist Source)
    (mass : Source → (Slot → Color) → ℝ) (cutoff : ℕ) (word : Slot → Color) :
    densityTail reference (mixtureMass source mass) cutoff word =
      source.expectation (fun sample => densityTail reference (mass sample) cutoff word) := by
  unfold densityTail
  simp only [densityComponent_mixture, FiniteDist.expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- Averaging the entire coefficient tail is an actual Hilbert contraction.
The mixture may be the exact normalized integer slice and shared queue law. -/
theorem symmetrized_mixture_tail_energy_le (reference : FiniteDist Color) (source : FiniteDist Source)
    (mass : Source → (Slot → Color) → ℝ) (cutoff : ℕ) :
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
      (densityTail reference (symmetrizedMass (mixtureMass source mass)) cutoff) ≤
      source.expectation (fun sample => (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
        (densityTail reference (symmetrizedMass (mass sample)) cutoff)) := by
  rw [symmetrizedMass_mixture]
  unfold FiniteDist.l2Sq
  simp only [densityTail_mixture]
  calc
    _ ≤ (FiniteDist.independent (fun _ : Slot => reference)).expectation (fun word =>
        source.expectation (fun sample => densityTail reference (symmetrizedMass (mass sample)) cutoff word ^ 2)) := by
      apply Finset.sum_le_sum
      intro word _
      exact mul_le_mul_of_nonneg_left (expectation_square_le source _) (FiniteDist.nonneg _ _)
    _ = _ := by
      unfold FiniteDist.expectation
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sample _
      apply Finset.sum_congr rfl
      intro word _
      ring

omit [Fintype Slot] [Fintype Source] in
/-- The signed histogram tail is constructed for arbitrary signed mass,
without a positivity or probability-mass premise. -/
theorem actual_signed_histogram_tail_identity {population : ℕ}
    (reference : FiniteDist Color) (hreference : ∀ color, 0 < reference.weight color)
    (mass : (Fin population → Color) → ℝ) (cutoff : ℕ) :
    ∃ histogramTail : Histogram population Color → ℝ,
      densityTail reference (symmetrizedMass mass) cutoff = histogramTail ∘ histogram ∧
      ((FiniteDist.independent (fun _ : Fin population => reference)).map histogram).l2Sq histogramTail =
        HistogramTail.likelihoodTailEnergy population cutoff
          (fun degree => BlockFock.tensorEnergy
            (LocalTensors.degreeTensor (fun _ : Fin population => reference) mass degree)) := by
  have hexchangeable := densityTail_exchangeable reference (symmetrizedMass mass)
    (symmetrizedMass_exchangeable mass) cutoff
  obtain ⟨tail, htail, hnorm⟩ := AFT.exchangeable_histogram_l2Sq
    (FiniteDist.independent (fun _ : Fin population => reference))
    (densityTail reference (symmetrizedMass mass) cutoff) hexchangeable
  refine ⟨tail, htail, ?_⟩
  rw [hnorm]
  have h := symmetrized_densityTail_energy reference hreference mass cutoff
  simp only [Fintype.card_fin] at h
  apply Eq.trans ?_ h
  unfold FiniteDist.l2Sq FiniteDist.expectation FiniteDist.independent
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- Renumbering arbitrary physical slots and then taking the histogram loses
no tail energy, including for the complete signed conditioned mixture. -/
theorem actual_signed_renamed_histogram_tail (reference : FiniteDist Color)
    (hreference : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (cutoff : ℕ) :
    ∃ histogramTail : Histogram (Fintype.card Slot) Color → ℝ,
      densityTail reference (symmetrizedMass (renamedMass (Fintype.equivFin Slot) mass)) cutoff =
        histogramTail ∘ histogram ∧
      ((FiniteDist.independent (fun _ : Fin (Fintype.card Slot) => reference)).map histogram).l2Sq histogramTail =
        (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
          (densityTail reference (symmetrizedMass mass) cutoff) := by
  obtain ⟨tail, htail, hnorm⟩ := actual_signed_histogram_tail_identity reference hreference
    (renamedMass (Fintype.equivFin Slot) mass) cutoff
  refine ⟨tail, htail, ?_⟩
  rw [hnorm, symmetrized_densityTail_energy reference hreference mass cutoff]
  unfold HistogramTail.likelihoodTailEnergy
  apply Finset.sum_congr rfl
  intro degree hdegree
  have hd : degree ≤ Fintype.card Slot :=
    Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hdegree).1)
  dsimp only
  rw [degreeTensor_renamedMass (Fintype.equivFin Slot) reference mass degree hd]

end AFT.HistogramNormalization

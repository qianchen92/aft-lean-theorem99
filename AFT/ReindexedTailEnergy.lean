import AFT.MixtureTail
import AFT.ReindexedFock

/-! # The complete physical tail is unchanged by any slot placement -/
namespace AFT.HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot OtherSlot Color : Type*} [Fintype Slot] [Fintype OtherSlot] [Fintype Color]

theorem symmetrized_renamed_tail_energy (equiv : Slot ≃ OtherSlot) (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color) (mass : (Slot → Color) → ℝ) (cutoff : ℕ) :
    (FiniteDist.independent (fun _ : OtherSlot => reference)).l2Sq
      (densityTail reference (symmetrizedMass (renamedMass equiv mass)) cutoff) =
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
      (densityTail reference (symmetrizedMass mass) cutoff) := by
  rw [symmetrized_densityTail_energy reference href, symmetrized_densityTail_energy reference href]
  unfold HistogramTail.likelihoodTailEnergy
  have hc := (Fintype.card_congr equiv).symm
  simp only [hc]
  apply Finset.sum_congr rfl
  intro degree hd
  have hd' : degree ≤ Fintype.card Slot :=
    Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
  rw [degreeTensor_renamedMass equiv reference mass degree hd']

end
end AFT.HistogramNormalization

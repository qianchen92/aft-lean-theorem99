import AFT.BlockProducts
import AFT.ReindexedCoefficients

/-! # The full histogram tail of the actual independent block sampler -/

namespace AFT
namespace BlockProducts

open scoped BigOperators Classical

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The physical independent block law on its actual numbered output slots. -/
noncomputable def indexedBlockLaw (law : (index : Index) → FiniteDist (Slots index → Color)) :
    FiniteDist (Fin (Fintype.card (Sigma Slots)) → Color) :=
  (blockLaw Slots law).map (HistogramNormalization.renameWord (Fintype.equivFin (Sigma Slots)))

set_option backward.isDefEq.respectTransparency false in
/-- Complete histogram tail for the actual uniformly relabeled independent
block sampler. The likelihood tail and its reference histogram law are both
constructed. Only the explicit local coefficient smallness conditions remain. -/
theorem actual_histogram_complete_tail [Nonempty Color]
    (reference : FiniteDist Color) (hreference : ∀ color, 0 < reference.weight color) (law : (index : Index) → FiniteDist (Slots index → Color))
    (hslots : ∀ index, Fintype.card (Slots index) ≤ 3) (cutoff capacity : ℕ) (radius : ℝ)
    (hpopulation : 0 < Fintype.card (Sigma Slots)) (hradius : Real.exp 1 ≤ radius ^ 2)
    (hcapacity : (SelectionBound.nonlinearSupport
      (normalizedQuadratic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))))
      (normalizedCubic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))))).card ≤ capacity)
    (henergy : (∑ index, ∑ color,
      normalizedLinear Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))) index color ^ 2) ≤ 1 / 8)
    (hsmall : (∑ index, (128 * SelectionBound.localPairNorm
      (normalizedQuadratic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots)))) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (normalizedCubic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots)))) index)) ≤ 1 / 2) :
    ∃ histogramTail : Histogram (Fintype.card (Sigma Slots)) Color → ℝ,
      HistogramNormalization.densityTail reference
        (AFT.symmetrize (indexedBlockLaw Slots law)).weight cutoff = histogramTail ∘ histogram ∧
      ((FiniteDist.independent (fun _ : Fin (Fintype.card (Sigma Slots)) => reference)).map histogram).l2Sq histogramTail ≤
      (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) *
        (16 * Real.exp (8 * ∑ color, (∑ index,
          normalizedLinear Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))) index color) ^ 2)) := by
  obtain ⟨tail, htail, hnorm⟩ := HistogramNormalization.actual_histogram_tail_identity
    reference hreference (indexedBlockLaw Slots law) cutoff
  refine ⟨tail, htail, ?_⟩
  rw [hnorm]
  have henergyEq :
      HistogramTail.likelihoodTailEnergy (Fintype.card (Sigma Slots)) cutoff
        (fun degree => BlockFock.tensorEnergy (LocalTensors.degreeTensor
          (fun _ : Fin (Fintype.card (Sigma Slots)) => reference) (indexedBlockLaw Slots law).weight degree)) =
      HistogramTail.likelihoodTailEnergy (Fintype.card (Sigma Slots)) cutoff
        (fun degree => BlockFock.tensorEnergy (LocalTensors.degreeTensor
          (fun _ : Sigma Slots => reference) (blockMass Slots law) degree)) := by
    unfold HistogramTail.likelihoodTailEnergy
    apply Finset.sum_congr rfl
    intro degree hdegree
    have hd : degree ≤ Fintype.card (Sigma Slots) := by
      have := (Finset.mem_filter.mp hdegree).1
      exact Nat.le_of_lt_succ (Finset.mem_range.mp this)
    have hmass : (indexedBlockLaw Slots law).weight =
        HistogramNormalization.renamedMass (Fintype.equivFin (Sigma Slots)) (blockMass Slots law) := by
      funext word
      unfold indexedBlockLaw
      rw [FiniteDist.map_equiv_weight]
      rfl
    simp only [hmass]
    congr 2
    exact congrArg BlockFock.tensorEnergy (HistogramNormalization.degreeTensor_renamedMass
      (Fintype.equivFin (Sigma Slots)) reference (blockMass Slots law) degree hd)
  rw [henergyEq]
  exact actual_block_complete_tail Slots reference law hslots cutoff capacity radius
    hpopulation hradius hcapacity henergy hsmall

end BlockProducts
end AFT

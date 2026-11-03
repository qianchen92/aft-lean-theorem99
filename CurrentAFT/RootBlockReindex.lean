import CurrentAFT.PairedRootCentering

/-! # Actual cycle components in physical block coordinates -/
namespace CurrentAFT.RootBlockReindex
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  PairedRootCentering CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

theorem actual_component_blocks {Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (test : (BlockIndex security → Root security) → Value) :
    actualComponent security (tagged.map layout.toEmbedding) (fun roots => test (roots ∘ layout)) =
      ∑ roots, ((FiniteDist.independent (fun _ : BlockIndex security => rootReference security)).weight roots *
        rootDensity selection tagged layout (roots ∘ rootEmbedding selection tagged)) • test roots := by
  rw [PairedRootInput.actual_component]
  rw [← (Equiv.piCongrLeft (fun _ : Vertex security => Root security) layout).sum_comp]
  apply Finset.sum_congr rfl
  intro roots _
  have hreindex : (Equiv.piCongrLeft (fun _ : Vertex security => Root security) layout roots) ∘ layout = roots := by
    funext block
    exact Equiv.piCongrLeft_apply_apply (fun _ : Vertex security => Root security) layout roots block
  have hweight : (FiniteDist.independent (fun _ : Vertex security => rootReference security)).weight
      (Equiv.piCongrLeft (fun _ : Vertex security => Root security) layout roots) =
      (FiniteDist.independent (fun _ : BlockIndex security => rootReference security)).weight roots := by
    simp only [FiniteDist.independent]
    rw [← Equiv.prod_comp layout]
    simp only [Equiv.piCongrLeft_apply_apply]
  rw [hweight, hreindex]
  congr 2
  unfold rootDensity
  congr 1
  funext index
  simp only [Function.comp_apply, labels_eq selection tagged layout, Equiv.piCongrLeft_apply_apply]

end
end CurrentAFT.RootBlockReindex

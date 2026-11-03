import CurrentAFT.RootConditionalComponent
import CurrentAFT.ActualRootDefect

/-! # Physical PGF of the complete actual root defect -/
namespace CurrentAFT.ActualRootDefectPhysical
open AFT ActualBlockFock TaggedSelection CycleRootExpansion ControlCoordinates
  LocalCoefficientFamily ActualRootDefect RootConditionalComponent
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance vertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) :=
  instDecidableEqFin (Parameters.bodySize security)
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def rootTest {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    (Vertex security → Root security) → MvPolynomial (ActualControls.Palette security) ℝ :=
  fun roots => TypedTaggedPhysical.conditionalPolynomial selection queue
    (fun block => (roots (layout block)).val) kernel.val

/-- The finite subset relabeling is an actual bijection; all root subsets,
including the large ones later killed by degree, remain in this equality. -/
theorem component_sum_reindex {Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    {security : ℕ} (layout : BlockIndex security ≃ Vertex security)
    (test : (Vertex security → Root security) → Value) :
    (∑ tagged ∈ (Finset.univ : Finset (Finset (BlockIndex security))).filter (fun tagged => 2 ≤ tagged.card),
      actualComponent security (tagged.map layout.toEmbedding) test) =
      ∑ tagged ∈ (Finset.univ : Finset (Finset (Vertex security))).filter (fun tagged => 2 ≤ tagged.card),
        actualComponent security tagged test := by
  simp only [Finset.sum_filter]
  rw [← layout.finsetCongr.sum_comp]
  simp only [Equiv.finsetCongr_apply, Finset.card_map]

/-- The true cycle law and the true independent reference differ by the
sum of the actual grouped physical root responses. -/
theorem selectedDefect_physical {security r s : ℕ} (order : ℕ) (horder : 2 ≤ order)
    (queue : ℤ) (selection : Selection security r s) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    BackgroundEvaluation.evaluation security order
      (ActualBackground.fixedQueueBackground security order horder queue *
        selectedDefect order (by omega) queue selection layout kernel) =
      TruncatedOutput.quotientMap order
        (expectationLinear (rootLaw security) (rootTest queue selection layout kernel) -
          expectationLinear (FiniteDist.independent (fun _ : Vertex security => rootReference security))
            (rootTest queue selection layout kernel)) := by
  rw [map_mul, BackgroundPolynomialEvaluation.fixedQueueBackground_image]
  simp only [selectedDefect, LinearMap.sum_apply, map_sum, Finset.mul_sum]
  have hlocal (tagged : Finset (BlockIndex security)) :
      TruncatedOutput.quotientMap order (BackgroundPolynomialEvaluation.fixedQueueGenerating security queue) *
        BackgroundEvaluation.evaluation security order
          (ActualRootResponse.response order (by omega) queue selection tagged layout kernel) =
      TruncatedOutput.quotientMap order (actualComponent security (tagged.map layout.toEmbedding)
        (rootTest queue selection layout kernel)) := by
    rw [mul_comm]
    exact response_physical_background order (by omega) queue selection tagged layout kernel
  simp_rw [hlocal]
  rw [← map_sum, component_sum_reindex layout (rootTest queue selection layout kernel)]
  have hdef := congrArg (fun response => response (rootTest queue selection layout kernel))
    (actual_response_defect (Value := MvPolynomial (ActualControls.Palette security) ℝ) security)
  simp only [LinearMap.sub_apply, LinearMap.sum_apply] at hdef
  congr 1
  refine Eq.trans ?_ hdef.symm
  apply Finset.sum_congr (by ext tagged; simp)
  intro tagged _
  rfl

end
end CurrentAFT.ActualRootDefectPhysical

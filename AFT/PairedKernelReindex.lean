import AFT.PairedPublicKernel
import AFT.CompatibleFibers

/-! # Reindexing joint paired scores without changing their public laws -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Source Target Input Public : Type*} [Fintype Source] [Fintype Target]
  [DecidableEq Source] [DecidableEq Target] [Fintype Input] [Fintype Public]

omit [Fintype Public] in
theorem matrixApply_reindex (equiv : Source ≃ Target) (matrix : Source → Input → Public → ℝ)
    (kernel : (Source → Input) → ℝ) (output : Target → Public) :
    matrixApply (fun slot => matrix (equiv.symm slot)) (fun input => kernel (input ∘ equiv)) output =
      matrixApply matrix kernel (output ∘ equiv) := by
  unfold matrixApply
  rw [← (HistogramNormalization.renameWord (Color := Input) equiv).sum_comp]
  apply Finset.sum_congr (by ext; simp)
  intro input _
  simp only [HistogramNormalization.renameWord,Equiv.coe_fn_mk,Function.comp_def,Equiv.symm_apply_apply]
  congr 1
  have he := equiv.prod_comp (fun slot => matrix (equiv.symm slot) (input (equiv.symm slot)) (output slot))
  simpa only [Equiv.symm_apply_apply] using he.symm
end
end AFT.MixedKernel

namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pairedReindexFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

theorem pairedPublicKernel_all_primary (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (count : ℕ) (kernel : (Fin count → Color) → ℝ) :
    pairedPublicKernel primary body anchor activation (fun _ : Fin count => true) kernel =
      TensorChannel.applyLinear count (fun _ => pairedPublicDensity primary body anchor activation) kernel := by
  funext output
  change _ = TensorChannel.apply count (fun _ => pairedPublicDensity primary body anchor activation) kernel output
  rw [TensorChannel.apply_formula]
  simp only [pairedPublicKernel,MixedKernel.matrixApply,pairedPublicDensity_single,publicInputMatrix,if_true]
  congr 2
  exact Subsingleton.elim _ _
end
end AFT

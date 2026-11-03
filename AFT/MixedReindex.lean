import AFT.MixedSymmetry
import AFT.TwoPoolCanonical

/-! # Full mixed activity under equivalences of actual input coordinates -/
namespace AFT.MixedKernel.CoordinateTransport
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Other Color : Type*} [Fintype Slot] [Fintype Other] [Fintype Color]
  [DecidableEq Slot] [DecidableEq Other]

def fixedEquiv (equiv : Slot ≃ Other) : Finset Other ≃ Finset Slot where
  toFun fixed := fixed.map equiv.symm.toEmbedding
  invFun fixed := fixed.map equiv.toEmbedding
  left_inv fixed := by ext slot; simp
  right_inv fixed := by ext slot; simp

theorem fiberSq_equiv (equiv : Slot ≃ Other) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Other) (values : Other → Color) :
    fiberSq (fun slot => reference (equiv.symm slot)) (fun word => kernel (word ∘ equiv)) fixed values =
      fiberSq reference kernel (fixed.map equiv.symm.toEmbedding) (values ∘ equiv) := by
  have hf (integrated : Other → Color) : freeze fixed values integrated ∘ equiv =
      freeze (fixed.map equiv.symm.toEmbedding) (values ∘ equiv) (integrated ∘ equiv) := by
    funext slot
    simp [freeze]
  unfold fiberSq FiniteDist.l2Sq
  simp only [hf]
  have he := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word : Slot → Color => (∏ slot, (reference slot).weight (word slot)) *
      kernel (freeze (fixed.map equiv.symm.toEmbedding) (values ∘ equiv) word) ^ 2)
  unfold FiniteDist.expectation FiniteDist.independent
  apply Eq.trans ?_ he
  apply Finset.sum_congr (by ext; simp)
  intro word _
  congr 1
  have hp := equiv.prod_comp (fun slot => (reference (equiv.symm slot)).weight (word slot))
  simpa only [Equiv.symm_apply_apply] using hp.symm

theorem fiberNorm_equiv (equiv : Slot ≃ Other) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Other) :
    fiberNorm (fun slot => reference (equiv.symm slot)) (fun word => kernel (word ∘ equiv)) fixed =
      fiberNorm reference kernel (fixed.map equiv.symm.toEmbedding) := by
  simp only [fiberNorm, fiberSq_equiv]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro values
    exact norm_le_pi_norm (fun values => Real.sqrt (fiberSq reference kernel (fixed.map equiv.symm.toEmbedding) values)) (values ∘ equiv)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro values
    have h := norm_le_pi_norm
      (fun values => Real.sqrt (fiberSq reference kernel (fixed.map equiv.symm.toEmbedding) (values ∘ equiv)))
      (values ∘ equiv.symm)
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using h

/-- Reindexing disjoint seed coordinates into a single finite input word
preserves all integrated and fixed fibers, with the exact same pool rates. -/
theorem activity_equiv (equiv : Slot ≃ Other) (rate : Slot → ℝ)
    (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ) :
    activity (fun slot => rate (equiv.symm slot)) (fun slot => reference (equiv.symm slot))
      (fun word => kernel (word ∘ equiv)) = activity rate reference kernel := by
  unfold activity
  have hp := equiv.symm.prod_comp rate
  rw [hp]
  congr 1
  simp only [fiberNorm_equiv]
  have he := (fixedEquiv equiv).sum_comp
    (fun fixed => (∏ slot ∈ fixed, rate slot) * fiberNorm reference kernel fixed)
  change (∑ fixed : Finset Other, (∏ slot ∈ fixed.map equiv.symm.toEmbedding, rate slot) *
    fiberNorm reference kernel (fixed.map equiv.symm.toEmbedding)) = _ at he
  simpa only [Finset.prod_map, Equiv.toEmbedding_apply] using he

omit [DecidableEq Slot] [DecidableEq Other] in
/-- Exact canonicality also survives a coordinate equivalence; it is not
replaced by a norm or moment assumption. -/
theorem canonical_equiv (equiv : Slot ≃ Other) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hc : Hoeffding.Canonical reference Finset.univ kernel) :
    Hoeffding.Canonical (fun slot => reference (equiv.symm slot)) Finset.univ
      (fun word => kernel (word ∘ equiv)) := by
  have he := CanonicalMoments.placedKernel_canonical_compatible
    (fun slot => reference (equiv.symm slot)) reference kernel hc equiv.toEmbedding (fun slot => by simp)
  have hu : Finset.univ.map equiv.toEmbedding = Finset.univ := by ext slot; simp
  rw [hu] at he
  exact he

end
end AFT.MixedKernel.CoordinateTransport

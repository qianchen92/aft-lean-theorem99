import AFT.CompatibleFibers

/-! # Exact mixed activity transport across different finite slot types -/

namespace AFT.MixedKernel

open scoped BigOperators Classical
open CanonicalMoments

noncomputable section

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]
  [DecidableEq Slot] [DecidableEq Pool]
  [Nonempty Color]

/-- Transport every coordinate reference and every fixed-coordinate set,
including between a disjoint union of slots and its finite numbering. -/
theorem fiberNorm_equiv (reference : Pool → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (equiv : Slot ≃ Pool) (fixed : Finset Pool) :
    fiberNorm reference (fun word => kernel (word ∘ equiv)) fixed =
      fiberNorm (fun slot => reference (equiv slot)) kernel (fixed.map equiv.symm.toEmbedding) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  cases Subsingleton.elim (inferInstance : DecidableEq Pool) (Classical.decEq Pool)
  have hfixed : placementFixed equiv.toEmbedding fixed = fixed.map equiv.symm.toEmbedding := by
    ext slot
    simp [placementFixed]
  simpa only [placedKernel, hfixed, Equiv.coe_toEmbedding] using
    placedKernel_fiberNorm_general reference kernel equiv.toEmbedding fixed

theorem activity_equiv (rate : Pool → ℝ) (reference : Pool → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (equiv : Slot ≃ Pool) :
    activity rate reference (fun word => kernel (word ∘ equiv)) =
      activity (fun slot => rate (equiv slot)) (fun slot => reference (equiv slot)) kernel := by
  classical
  unfold activity
  rw [← Equiv.prod_comp equiv rate]
  congr 1
  simp only [fiberNorm_equiv reference kernel equiv]
  have hp (fixed : Finset Pool) :
      (∏ slot ∈ fixed.map equiv.symm.toEmbedding, rate (equiv slot)) = ∏ slot ∈ fixed, rate slot := by
    simp only [Finset.prod_map, Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
  have hh := Equiv.sum_comp (Equiv.finsetCongr equiv.symm)
    (fun fixed => (∏ slot ∈ fixed, rate (equiv slot)) *
      fiberNorm (fun slot => reference (equiv slot)) kernel fixed)
  change (∑ fixed : Finset Pool,
    (∏ slot ∈ fixed.map equiv.symm.toEmbedding, rate (equiv slot)) *
      fiberNorm (fun slot => reference (equiv slot)) kernel (fixed.map equiv.symm.toEmbedding)) = _ at hh
  simpa only [hp] using hh

end

end AFT.MixedKernel

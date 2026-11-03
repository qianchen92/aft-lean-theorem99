import AFT.MixedTensor

/-! # Symmetrization contracts full mixed input activity -/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def wordPerm (permutation : Equiv.Perm Slot) : (Slot → Color) ≃ (Slot → Color) where
  toFun word := word ∘ permutation
  invFun word := word ∘ permutation.symm
  left_inv word := by ext slot; simp
  right_inv word := by ext slot; simp

theorem independent_map_wordPerm (reference : Slot → FiniteDist Color)
    (permutation : Equiv.Perm Slot) (hreference : ∀ slot, reference (permutation slot) = reference slot) :
    (FiniteDist.independent reference).map (wordPerm permutation) = FiniteDist.independent reference := by
  ext word
  rw [FiniteDist.map_equiv_weight]
  change (∏ slot, (reference slot).weight (word (permutation.symm slot))) = ∏ slot, (reference slot).weight (word slot)
  have h := Equiv.prod_comp permutation (fun slot => (reference slot).weight (word (permutation.symm slot)))
  simpa only [hreference, Equiv.symm_apply_apply] using h.symm

omit [Fintype Slot] [Fintype Color] in
theorem freeze_reindex (fixed : Finset Slot) (permutation : Equiv.Perm Slot)
    (values integrated : Slot → Color) :
    freeze fixed values integrated ∘ permutation =
      freeze (fixed.map permutation.symm.toEmbedding) (values ∘ permutation) (integrated ∘ permutation) := by
  ext slot
  have hm : slot ∈ fixed.map permutation.symm.toEmbedding ↔ permutation slot ∈ fixed := by simp
  simp only [Function.comp_apply, freeze, hm]

theorem fiberSq_reindex (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (permutation : Equiv.Perm Slot)
    (hreference : ∀ slot, reference (permutation slot) = reference slot) (values : Slot → Color) :
    fiberSq reference (fun word => kernel (word ∘ permutation)) fixed values =
      fiberSq reference kernel (fixed.map permutation.symm.toEmbedding) (values ∘ permutation) := by
  have h := (FiniteDist.independent reference).l2Sq_map (wordPerm permutation)
    (fun integrated => kernel (freeze (fixed.map permutation.symm.toEmbedding) (values ∘ permutation) integrated))
  rw [independent_map_wordPerm reference permutation hreference] at h
  simpa only [fiberSq, Function.comp_apply, wordPerm, freeze_reindex] using h.symm

theorem fiberNorm_reindex (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (permutation : Equiv.Perm Slot)
    (hreference : ∀ slot, reference (permutation slot) = reference slot) :
    fiberNorm reference (fun word => kernel (word ∘ permutation)) fixed =
      fiberNorm reference kernel (fixed.map permutation.symm.toEmbedding) := by
  simp only [fiberNorm, fiberSq_reindex reference kernel fixed permutation hreference]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro values
    exact norm_le_pi_norm (fun values => Real.sqrt (fiberSq reference kernel
      (fixed.map permutation.symm.toEmbedding) values)) (values ∘ permutation)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro values
    have h := norm_le_pi_norm
      (fun values => Real.sqrt (fiberSq reference kernel (fixed.map permutation.symm.toEmbedding)
        (values ∘ permutation))) (values ∘ permutation.symm)
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using h

def fixedPerm (permutation : Equiv.Perm Slot) : Equiv.Perm (Finset Slot) where
  toFun fixed := fixed.map permutation.symm.toEmbedding
  invFun fixed := fixed.map permutation.toEmbedding
  left_inv fixed := by ext slot; simp
  right_inv fixed := by ext slot; simp

theorem activity_reindex (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (permutation : Equiv.Perm Slot)
    (hrate : ∀ slot, rate (permutation slot) = rate slot)
    (hreference : ∀ slot, reference (permutation slot) = reference slot) :
    activity rate reference (fun word => kernel (word ∘ permutation)) = activity rate reference kernel := by
  unfold activity
  congr 1
  simp only [fiberNorm_reindex reference kernel _ permutation hreference]
  have hp (fixed : Finset Slot) : (∏ i ∈ fixed.map permutation.symm.toEmbedding, rate i) =
      ∏ i ∈ fixed, rate i := by
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro slot _
    exact (hrate (permutation.symm slot)).symm.trans (congrArg rate (permutation.apply_symm_apply slot))
  have h := Equiv.sum_comp (fixedPerm permutation)
    (fun fixed => (∏ i ∈ fixed, rate i) * fiberNorm reference kernel fixed)
  change (∑ fixed : Finset Slot, (∏ i ∈ fixed.map permutation.symm.toEmbedding, rate i) *
    fiberNorm reference kernel (fixed.map permutation.symm.toEmbedding)) = _ at h
  simpa only [hp] using h

end

end AFT.MixedKernel

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color Tag : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

set_option backward.isDefEq.respectTransparency false in
theorem activity_sum_le (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : Tag → (Slot → Color) → ℝ) (tags : Finset Tag) (hrate : ∀ slot, 0 ≤ rate slot) :
    activity rate reference (∑ tag ∈ tags, kernel tag) ≤ ∑ tag ∈ tags, activity rate reference (kernel tag) := by
  induction tags using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, activity_zero, le_refl]
  | @insert tag tags hnot ih =>
    simp only [Finset.sum_insert hnot]
    exact (activity_add_le rate reference (kernel tag) (∑ t ∈ tags, kernel t) hrate).trans
      (add_le_add (le_refl (activity rate reference (kernel tag))) ih)

variable [Fintype Tag]

/-- Finite averages contract the actual input norm, using the sum over
all fixed-coordinate sets. -/
theorem activity_average_le (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : Tag → (Slot → Color) → ℝ) (law : FiniteDist Tag) (hrate : ∀ slot, 0 ≤ rate slot) :
    activity rate reference (∑ tag, law.weight tag • kernel tag) ≤
      ∑ tag, law.weight tag * activity rate reference (kernel tag) := by
  have h := activity_sum_le rate reference (fun tag => law.weight tag • kernel tag) Finset.univ hrate
  simpa only [activity_smul, abs_of_nonneg (law.nonneg _)] using h

/-- Any law on pool-preserving permutations contracts activity. Uniform
symmetrization and disjoint allocation averages are special cases. -/
theorem activity_symmetrization_le (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (law : FiniteDist Tag) (permutation : Tag → Equiv.Perm Slot)
    (hrate : ∀ slot, 0 ≤ rate slot)
    (hratePerm : ∀ tag slot, rate (permutation tag slot) = rate slot)
    (hreference : ∀ tag slot, reference (permutation tag slot) = reference slot) :
    activity rate reference (∑ tag, law.weight tag • (fun word => kernel (word ∘ permutation tag))) ≤
      activity rate reference kernel := by
  have h := activity_average_le rate reference (fun tag word => kernel (word ∘ permutation tag)) law hrate
  simp only [activity_reindex rate reference kernel _ (hratePerm _) (hreference _),
    ← Finset.sum_mul, law.sum_one, one_mul] at h
  exact h

end

end AFT.MixedKernel

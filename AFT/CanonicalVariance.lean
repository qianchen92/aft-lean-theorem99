import AFT.CanonicalMoments
import AFT.ReindexedCoefficients

/-! # Exact finite-pool variance for actual canonical subset statistics -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]

/-- A selected set, in a fixed ordering, is an actual injective pool placement. -/
noncomputable def subsetPlacement (selected : Finset Pool)
    (hcard : Fintype.card selected = Fintype.card Slot) : Slot ↪ Pool :=
  (Fintype.equivOfCardEq hcard).symm.toEmbedding.trans (Function.Embedding.subtype _)

omit [Fintype Color] [Fintype Pool] in
/-- The placement uses exactly its selected sample labels. -/
theorem subsetPlacement_image (selected : Finset Pool)
    (hcard : Fintype.card selected = Fintype.card Slot) :
    Finset.univ.map (subsetPlacement (Slot := Slot) selected hcard) = selected := by
  ext label
  constructor
  · intro h
    obtain ⟨slot, _, rfl⟩ := Finset.mem_map.mp h
    exact ((Fintype.equivOfCardEq hcard).symm slot).property
  · intro h
    refine Finset.mem_map.mpr ⟨(Fintype.equivOfCardEq hcard) ⟨label, h⟩, Finset.mem_univ _, ?_⟩
    simp [subsetPlacement]

/-- The selected joint kernel is evaluated on its actual distinct pool slots. -/
noncomputable def subsetKernel (kernel : (Slot → Color) → ℝ) (selected : Finset Pool)
    (word : Pool → Color) : ℝ :=
  if hcard : Fintype.card selected = Fintype.card Slot then
    placedKernel kernel (subsetPlacement selected hcard) word else 0

omit [Fintype Pool] in
/-- Every selected kernel is canonical on its own selected coordinate set. -/
theorem subsetKernel_canonical (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Slot => reference) Finset.univ kernel)
    (selected : Finset Pool) (hcard : Fintype.card selected = Fintype.card Slot) :
    Hoeffding.Canonical (fun _ : Pool => reference) selected (subsetKernel kernel selected) := by
  have h := placedKernel_canonical reference kernel hcanonical (subsetPlacement selected hcard)
  rw [subsetPlacement_image] at h
  have heq : subsetKernel kernel selected = placedKernel kernel (subsetPlacement selected hcard) := by
    funext word
    simp only [subsetKernel, dif_pos hcard]
  rw [heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Renaming independent, identically distributed coordinates preserves the
actual finite expectation, including its weights. -/
theorem independent_equiv_expectation (equiv : Slot ≃ Pool) (reference : FiniteDist Color)
    (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation
      (fun word => function (word ∘ equiv)) =
      (FiniteDist.independent (fun _ : Slot => reference)).expectation function := by
  have h := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word => (∏ slot, reference.weight (word slot)) * function word)
  unfold FiniteDist.expectation FiniteDist.independent
  apply Eq.trans ?_ h
  apply Finset.sum_congr (by ext; simp)
  intro word _
  change (∏ slot, reference.weight (word slot)) * function (word ∘ equiv) =
    (∏ slot, reference.weight ((word ∘ equiv) slot)) * function (word ∘ equiv)
  congr 1
  exact (equiv.prod_comp (fun slot => reference.weight (word slot))).symm

set_option backward.isDefEq.respectTransparency false in
/-- A selected kernel has exactly the original joint-kernel squared norm. -/
theorem subsetKernel_l2Sq (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (selected : Finset Pool) (hcard : Fintype.card selected = Fintype.card Slot) :
    (FiniteDist.independent (fun _ : Pool => reference)).l2Sq (subsetKernel kernel selected) =
      (FiniteDist.independent (fun _ : Slot => reference)).l2Sq kernel := by
  simp only [FiniteDist.l2Sq, subsetKernel, dif_pos hcard]
  have hr := LocalTensors.independent_restriction_expectation
    (fun _ : Pool => reference) selected
      (fun word : selected → Color => (kernel (word ∘ (Fintype.equivOfCardEq hcard).symm)) ^ 2)
  apply Eq.trans ?_ (hr.trans ?_)
  · rfl
  · have h := independent_equiv_expectation (Fintype.equivOfCardEq hcard).symm reference (fun word => kernel word ^ 2)
    apply Eq.trans ?_ h
    unfold FiniteDist.expectation FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rfl

/-- The exactly normalized average over all unordered distinct sample sets. -/
noncomputable def subsetStatistic (kernel : (Slot → Color) → ℝ) (word : Pool → Color) : ℝ :=
  (∑ selected ∈ Finset.univ.powersetCard (Fintype.card Slot), subsetKernel kernel selected word) /
    ((Fintype.card Pool).choose (Fintype.card Slot) : ℝ)

/-- Exact canonical variance, without supplying a norm-identification premise
or replacing the finite binomial normalizer by a power of the pool size. -/
theorem subsetStatistic_variance (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Slot => reference) Finset.univ kernel) :
    (FiniteDist.independent (fun _ : Pool => reference)).l2Sq (subsetStatistic kernel) =
      (FiniteDist.independent (fun _ : Slot => reference)).l2Sq kernel /
        ((Fintype.card Pool).choose (Fintype.card Slot) : ℝ) := by
  have hcard (selected : Finset Pool)
      (hselected : selected ∈ Finset.univ.powersetCard (Fintype.card Slot)) :
      Fintype.card selected = Fintype.card Slot := by
    simpa only [Fintype.card_coe] using (Finset.mem_powersetCard.mp hselected).2
  have h := Hoeffding.canonical_average_l2Sq (fun _ : Pool => reference)
    (Finset.univ.powersetCard (Fintype.card Slot)) (subsetKernel kernel)
    (fun selected hselected => subsetKernel_canonical reference kernel hcanonical selected (hcard selected hselected))
    ((FiniteDist.independent (fun _ : Slot => reference)).l2Sq kernel)
    (fun selected hselected => subsetKernel_l2Sq reference kernel selected (hcard selected hselected))
  simpa only [Finset.card_powersetCard, Finset.card_univ, subsetStatistic] using h

end AFT.CanonicalMoments

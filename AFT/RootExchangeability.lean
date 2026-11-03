import AFT.RootWindow
import AFT.MixedSymmetry

/-! # Exact coordinate symmetry of the conditioned integer root law -/

namespace AFT.RootSlice

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Color Slot Pool : Type*} [Fintype Color] [Fintype Slot] [Fintype Pool]

omit [Fintype Pool] in
theorem probability_const_formula (source : FiniteDist Color) (score : Color → ℤ) (target : ℤ) :
    probability (fun _ : Slot => source) score target =
      ∑ word : Slot → Color, if integerSum score word = target then ∏ slot, source.weight (word slot) else 0 := by
  unfold probability FiniteDist.eventMass FiniteDist.independent
  apply Finset.sum_congr rfl
  intro word _
  split_ifs <;> rfl

/-- Relabeling the coordinates leaves the actual iid integer-sum probability
unchanged, including its exact finite normalizer. -/
theorem probability_const_equiv (source : FiniteDist Color) (score : Color → ℤ)
    (target : ℤ) (equiv : Slot ≃ Pool) :
    probability (fun _ : Slot => source) score target =
      probability (fun _ : Pool => source) score target := by
  have hh := Equiv.sum_comp (Equiv.arrowCongr equiv (Equiv.refl Color))
    (fun word : Pool → Color => if integerSum score word = target then ∏ slot, source.weight (word slot) else 0)
  rw [probability_const_formula, probability_const_formula]
  apply Eq.trans ?_ hh
  apply Finset.sum_congr (by ext; simp)
  intro word _
  have hs : integerSum score ((Equiv.arrowCongr equiv (Equiv.refl Color)) word) = integerSum score word := by
    simp only [integerSum, Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply]
    exact Equiv.sum_comp equiv.symm (fun slot => score (word slot))
  have hp : (∏ slot, source.weight (((Equiv.arrowCongr equiv (Equiv.refl Color)) word) slot)) =
      ∏ slot, source.weight (word slot) := by
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply]
    exact Equiv.prod_comp equiv.symm (fun slot => source.weight (word slot))
  simp only [hs, hp]

omit [Fintype Pool] in
/-- The full joint law itself, not just its marginals, is exchangeable. -/
theorem law_map_wordPerm (source : FiniteDist Color) (score : Color → ℤ) (target : ℤ)
    (hprob : 0 < probability (fun _ : Slot => source) score target) (permutation : Equiv.Perm Slot) :
    (law (fun _ : Slot => source) score target hprob).map (MixedKernel.wordPerm permutation) =
      law (fun _ : Slot => source) score target hprob := by
  ext word
  rw [FiniteDist.map_equiv_weight]
  have hs : integerSum score ((MixedKernel.wordPerm permutation).symm word) = integerSum score word :=
    Equiv.sum_comp permutation.symm (fun slot => score (word slot))
  have hp : (∏ slot, source.weight (((MixedKernel.wordPerm permutation).symm word) slot)) =
      ∏ slot, source.weight (word slot) :=
    Equiv.prod_comp permutation.symm (fun slot => source.weight (word slot))
  simp only [law, FiniteDist.condition, FiniteDist.independent, hs, hp]

omit [Fintype Pool] in
/-- Every coordinate marginal equals the previously defined population
root marginal, with the same conditioning normalizer. -/
theorem reference_eq_marginalLaw (source : FiniteDist Color) (score : Color → ℤ) (slot : Slot)
    (hprob : 0 < probability (fun _ : Slot => source) score 0) :
    reference (fun _ : Slot => source) score 0 hprob slot =
      marginalLaw source score (Fintype.card Slot)
        (Fintype.card_pos_iff.mpr ⟨slot⟩)
        (by
          have heq := probability_const_equiv source score 0 (Fintype.equivFin Slot)
          change 0 < probability (fun _ : Fin (Fintype.card Slot) => source) score 0
          rw [← heq]
          exact hprob) := by
  have hrest : Fintype.card {j : Slot // j ≠ slot} = Fintype.card Slot - 1 := by
    simp [Fintype.card_subtype_compl]
  let equiv : {j : Slot // j ≠ slot} ≃ Fin (Fintype.card Slot - 1) :=
    Fintype.equivOfCardEq (by simp [hrest])
  have hden := probability_const_equiv source score 0 (Fintype.equivFin Slot)
  ext color
  rw [reference_weight, marginalLaw_weight]
  have hnum : (∑ rest : {j : Slot // j ≠ slot} → Color,
      if (∑ j, score (rest j)) = -score color then ∏ j, source.weight (rest j) else 0) =
      sumProbability source score (Fintype.card Slot - 1) (-score color) := by
    calc
      _ = probability (fun _ : {j : Slot // j ≠ slot} => source) score (-score color) := by
        rw [probability_const_formula]
        apply Finset.sum_congr (by ext; simp)
        intro rest _
        rfl
      _ = _ := probability_const_equiv source score (-score color) equiv
  simp only [zero_sub]
  rw [hnum]
  change source.weight color / probability (fun _ : Slot => source) score 0 * _ = _
  rw [hden]
  unfold sumProbability
  ring

end
end AFT.RootSlice

namespace AFT.GaussianSource

noncomputable local instance rootExchangeabilityFinDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Every literal coordinate of the actual clipped, zero-sum Gaussian root
vector has exactly `rootMarginal`, for every finite population. -/
theorem root_joint_coordinate_map (width : ℝ) (cutoff population : ℕ) (hpopulation : 0 < population)
    (slot : Fin population) :
    (RootSlice.law (fun _ : Fin population => windowGaussian width cutoff) (fun sample => (sample : ℤ)) 0
      (window_root_probability_positive width cutoff population)).map (fun word => word slot) =
        rootMarginal width cutoff population hpopulation := by
  have hh := RootSlice.reference_eq_marginalLaw (windowGaussian width cutoff) (fun sample => (sample : ℤ)) slot
    (window_root_probability_positive width cutoff population)
  simpa only [RootSlice.reference, Fintype.card_fin, rootMarginal] using hh

theorem root_joint_coordinate_expectation (width : ℝ) (cutoff population : ℕ) (hpopulation : 0 < population)
    (slot : Fin population) (value : Window cutoff → ℝ) :
    (RootSlice.law (fun _ : Fin population => windowGaussian width cutoff) (fun sample => (sample : ℤ)) 0
      (window_root_probability_positive width cutoff population)).expectation (fun word => value (word slot)) =
        (rootMarginal width cutoff population hpopulation).expectation value := by
  rw [← root_joint_coordinate_map width cutoff population hpopulation slot, FiniteDist.expectation_map]
  rfl

end
end AFT.GaussianSource

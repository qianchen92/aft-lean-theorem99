import AFT.RootWindow

/-!
# Exact sign reversal of the clipped Gaussian and the conditioned root marginal
-/

namespace AFT

open scoped BigOperators

namespace RootSlice

noncomputable section

local instance (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

set_option backward.isDefEq.respectTransparency false in
theorem sumProbability_reflection {α : Type*} [Fintype α]
    (source : FiniteDist α) (score : α → ℤ) (reverse : α ≃ α)
    (hw : ∀ value, source.weight (reverse value) = source.weight value)
    (hs : ∀ value, score (reverse value) = -score value) (count : ℕ) (target : ℤ) :
    sumProbability source score count (-target) = sumProbability source score count target := by
  classical
  unfold sumProbability probability FiniteDist.eventMass FiniteDist.independent
  dsimp only
  apply Finset.sum_bij (fun vector _ => fun index => reverse (vector index))
  · intro vector _
    exact Finset.mem_univ _
  · intro first _ second _ heq
    funext index
    exact reverse.injective (congrFun heq index)
  · intro vector _
    refine ⟨fun index => reverse.symm (vector index), Finset.mem_univ _, ?_⟩
    funext index
    exact reverse.apply_symm_apply _
  · intro vector _
    have hsum : integerSum score (fun index => reverse (vector index)) = -integerSum score vector := by
      simp only [integerSum, hs, Finset.sum_neg_distrib]
    have hproduct : (∏ index, source.weight (reverse (vector index))) = ∏ index, source.weight (vector index) := by
      simp only [hw]
    dsimp only
    have hh : integerSum score vector = -target ↔ -integerSum score vector = target := by omega
    simp only [hsum, hproduct, hh]

end

end RootSlice

namespace GaussianSource

noncomputable def windowNegateEquiv (cutoff : ℕ) : Window cutoff ≃ Window cutoff where
  toFun := windowNegate cutoff
  invFun := windowNegate cutoff
  left_inv value := by apply Subtype.ext; simp [windowNegate]
  right_inv value := by apply Subtype.ext; simp [windowNegate]

@[simp] theorem windowNegateEquiv_val (cutoff : ℕ) (value : Window cutoff) :
    ((windowNegateEquiv cutoff value : Window cutoff) : ℤ) = -(value : ℤ) := rfl

theorem windowGaussian_reflection (width : ℝ) (cutoff : ℕ) (value : Window cutoff) :
    (windowGaussian width cutoff).weight (windowNegateEquiv cutoff value) =
      (windowGaussian width cutoff).weight value := by
  simp only [windowGaussian, FiniteDist.normalize, windowNegateEquiv_val, weight, Int.cast_neg, neg_sq]

/-- Conditioning the actual independent Gaussian product on integer sum
zero preserves exact sign reversal of every true marginal. -/
theorem rootMarginal_reflection (width : ℝ) (cutoff population : ℕ)
    (hpopulation : 0 < population) (value : Window cutoff) :
    (rootMarginal width cutoff population hpopulation).weight (windowNegateEquiv cutoff value) =
      (rootMarginal width cutoff population hpopulation).weight value := by
  unfold rootMarginal
  rw [RootSlice.marginalLaw_weight, RootSlice.marginalLaw_weight, windowGaussian_reflection]
  simp only [windowNegateEquiv_val, neg_neg]
  rw [RootSlice.sumProbability_reflection (windowGaussian width cutoff) (fun value => (value : ℤ))
    (windowNegateEquiv cutoff) (windowGaussian_reflection width cutoff) (fun _ => rfl)]

end GaussianSource
end AFT

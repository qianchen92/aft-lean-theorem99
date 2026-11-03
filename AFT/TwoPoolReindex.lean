import AFT.TwoPoolCanonical

/-! # Exact invariance of two-pool statistics under finite coordinate names -/
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {PS BS PS' BS' PP BP PP' BP' Color : Type*}
  [Fintype PS] [Fintype BS] [Fintype PS'] [Fintype BS']
  [Fintype PP] [Fintype BP] [Fintype PP'] [Fintype BP'] [Fintype Color]

omit [Fintype Color] in
theorem twoPoolStatistic_reindex (primary : PS ≃ PS') (body : BS ≃ BS')
    (primaryPool : PP ≃ PP') (bodyPool : BP ≃ BP')
    (kernel : (PS ⊕ BS → Color) → ℝ) (word : PP' ⊕ BP' → Color) :
    twoPoolStatistic (fun input => kernel (input ∘ Equiv.sumCongr primary body)) word=
      twoPoolStatistic kernel (word ∘ Equiv.sumCongr primaryPool bodyPool) := by
  let choices := Equiv.prodCongr (Equiv.embeddingCongr primary primaryPool)
    (Equiv.embeddingCongr body bodyPool)
  unfold twoPoolStatistic
  rw [← Fintype.card_congr primary,← Fintype.card_congr body,
    ← Fintype.card_congr primaryPool,← Fintype.card_congr bodyPool]
  congr 1
  rw [← choices.sum_comp]
  apply Finset.sum_congr rfl
  intro choice _
  unfold placedKernel
  dsimp only
  apply congrArg kernel
  funext slot
  cases slot <;> simp [choices,Equiv.embeddingCongr,Function.comp_def]

end
end AFT.CanonicalMoments

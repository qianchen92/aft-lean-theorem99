import AFT.MixedSingleton

/-! # Literal singleton activities for signed profiles on partial supports -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

theorem profile_singleton_activity_le (reference : FiniteDist Color) (profile : Color → ℝ)
    (rate full fixed : ℝ) (hrate : 0 ≤ rate) (hfull : 0 ≤ full) (hfixed : 0 ≤ fixed)
    (hfullSq : profileSquareNorm reference.weight profile ≤ full^2)
    (hpoint : ∀ color, |profile color| ≤ fixed*reference.weight color) :
    activity (fun _ : Fin 1 => rate) (fun _ => reference)
      (singletonKernel (fun color => profile color/reference.weight color)) ≤ rate*(full+rate*fixed) := by
  apply singleton_activity_le reference _ rate full fixed hrate hfull hfixed
  · have heq : (∑ color, reference.weight color*(profile color/reference.weight color)^2) =
        profileSquareNorm reference.weight profile := by
      unfold profileSquareNorm
      apply Finset.sum_congr rfl
      intro color _
      field_simp
    rw [heq]
    exact hfullSq
  · intro color
    by_cases hz : reference.weight color = 0
    · simp only [hz,div_zero,abs_zero]
      exact hfixed
    · have hp : 0 < reference.weight color := lt_of_le_of_ne (reference.nonneg color) (Ne.symm hz)
      rw [abs_div,abs_of_pos hp]
      exact (div_le_iff₀ hp).mpr (hpoint color)

end
end AFT.MixedKernel

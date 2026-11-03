import AFT.RootConvolutionProgram
import AFT.FiniteProductVariation

/-! # Scalar numerical error propagates through actual root convolution -/
namespace AFT.RootSlice
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootConvolutionStabilityFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Source : Type*} [Fintype Source]

/-- Absolute error in an exact remaining-sum probability costs at most one
scalar L1 error per convolution, uniformly over all integer targets. -/
theorem sumProbability_l1_error (first second : FiniteDist Source)
    (score : Source → ℤ) (count : ℕ) (target : ℤ) :
    |sumProbability first score count target-sumProbability second score count target| ≤
      (count : ℝ)*(∑ point,|first.weight point-second.weight point|) := by
  have hprod : (∑ word : Fin count → Source,
      |(FiniteDist.independent (fun _ : Fin count => first)).weight word-
        (FiniteDist.independent (fun _ : Fin count => second)).weight word|) ≤
      (count : ℝ)*(∑ point,|first.weight point-second.weight point|) := by
    convert FiniteDist.l1_independent_fin_le count (fun _ => first) (fun _ => second) using 1
    · apply Finset.sum_congr (by ext; simp)
      intro word _
      rfl
    · simp
  apply le_trans _ hprod
  unfold sumProbability probability FiniteDist.eventMass
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro word _
  split_ifs
  · rfl
  · simp only [sub_self,abs_zero,abs_nonneg]

/-- The full conditioned root law is stable as soon as its one normalizer
is controlled. No inverse one-root atom enters this theorem. -/
theorem conditioned_root_l1_error (first second : FiniteDist Source)
    (score : Source → ℤ) (count : ℕ) (target : ℤ) (error lower : ℝ)
    (hscalar : (∑ point,|first.weight point-second.weight point|) ≤ error)
    (hlower : 0 < lower) (hevent : lower ≤ sumProbability second score count target)
    (hsmall : 2*((count : ℝ)*error) ≤ lower/2) :
    ∃ hfirst : 0 < sumProbability first score count target,
      FiniteDist.TVBound (law (fun _ : Fin count => first) score target hfirst)
        (law (fun _ : Fin count => second) score target (hlower.trans_le hevent))
        (4*((count : ℝ)*error)/lower) := by
  have he0 : 0 ≤ error := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hscalar
  have hprod : FiniteDist.TVBound (FiniteDist.independent (fun _ : Fin count => first))
      (FiniteDist.independent (fun _ : Fin count => second)) ((count : ℝ)*error) := by
    apply (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr
    rw [FiniteDist.totalVariation_eq_half_l1]
    have h : (∑ word : Fin count → Source,
        |(FiniteDist.independent (fun _ : Fin count => first)).weight word-
          (FiniteDist.independent (fun _ : Fin count => second)).weight word|) ≤
        (count : ℝ)*(∑ point,|first.weight point-second.weight point|) := by
      convert FiniteDist.l1_independent_fin_le count (fun _ => first) (fun _ => second) using 1
      · apply Finset.sum_congr (by ext; simp)
        intro word _
        rfl
      · simp
    have hh := h.trans (mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg count))
    linarith [mul_nonneg (Nat.cast_nonneg count) he0]
  exact hprod.condition (fun word => integerSum score word=target) hlower hevent hsmall

end
end AFT.RootSlice

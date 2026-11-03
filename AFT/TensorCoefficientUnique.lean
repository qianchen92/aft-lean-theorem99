import AFT.TensorFock

/-! # Uniqueness of exact finite symmetric tensor coefficients -/

namespace AFT
namespace TensorFock

open MeasureTheory
open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Exact real tensor subtraction evaluates to complex polynomial subtraction. -/
theorem tensorEvaluation_sub (first second : BlockFock.Tensor Slot Color) (value : Color → ℂ) :
    tensorEvaluation (fun word => first word - second word) value =
      tensorEvaluation first value - tensorEvaluation second value := by
  simp only [tensorEvaluation, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]

omit [Fintype Slot] in
set_option backward.isDefEq.respectTransparency false in
/-- The proved Gaussian all-degree isometry makes symmetric tensor
coefficients unique; no formal-polynomial axiom is used. -/
theorem series_coefficients_unique (degrees : Finset ℕ)
    (first second : (degree : ℕ) → BlockFock.Tensor (Fin degree) Color)
    (hfirst : ∀ degree ∈ degrees, ∀ word (permutation : Equiv.Perm (Fin degree)),
      first degree (word ∘ permutation) = first degree word)
    (hsecond : ∀ degree ∈ degrees, ∀ word (permutation : Equiv.Perm (Fin degree)),
      second degree (word ∘ permutation) = second degree word)
    (hevaluation : ∀ value, seriesEvaluation degrees first value = seriesEvaluation degrees second value)
    (degree : ℕ) (hdegree : degree ∈ degrees) : first degree = second degree := by
  let difference (degree : ℕ) (word : Fin degree → Color) := first degree word - second degree word
  have hsymmetric : ∀ order ∈ degrees, ∀ word (permutation : Equiv.Perm (Fin order)),
      difference order (word ∘ permutation) = difference order word := by
    intro order horder word permutation
    dsimp [difference]
    rw [hfirst order horder, hsecond order horder]
  have hzero (value : Color → ℂ) : seriesEvaluation degrees difference value = 0 := by
    simp only [seriesEvaluation, difference, tensorEvaluation_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hevaluation value)
  have hisometry := complete_tensor_fock_isometry degrees difference hsymmetric
  simp only [hzero, map_zero, integral_zero] at hisometry
  have hsingle := Finset.single_le_sum
    (f := fun order => (order.factorial : ℝ) * BlockFock.tensorEnergy (difference order))
    (fun order _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hdegree
  rw [← hisometry] at hsingle
  have hfactorial : (0 : ℝ) < degree.factorial := by exact_mod_cast degree.factorial_pos
  have henergy : BlockFock.tensorEnergy (difference degree) = 0 := by
    have hnonneg : 0 ≤ BlockFock.tensorEnergy (difference degree) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  funext word
  letI : DecidableEq (Fin degree) := Classical.decEq _
  have hword := Finset.single_le_sum (f := fun word => difference degree word ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ word)
  change difference degree word ^ 2 ≤ BlockFock.tensorEnergy (difference degree) at hword
  rw [henergy] at hword
  dsimp [difference] at hword
  nlinarith

end TensorFock
end AFT

import AFT.SafePairCore
import AFT.FiniteConvolution

/-! # Exact Hilbert contraction of the real core-supported canonical seed -/

namespace AFT.SafePair

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def centerOnCore (core : Finset ι) (profile : ι → ℝ) (color : ι) : ℝ :=
  profile color - uniformFiniteProfile core color * ∑ x, profile x

theorem centerOnCore_supported (core : Finset ι) (profile : ι → ℝ)
    (hsupport : ∀ color, color ∉ core → profile color = 0) (color : ι) (hout : color ∉ core) :
    centerOnCore core profile color = 0 := by simp [centerOnCore, uniformFiniteProfile, hout, hsupport color hout]

/-- Core centering is the genuine orthogonal projection in counting L2,
including its exact energy decrement. -/
theorem centerOnCore_square (core : Finset ι) (profile : ι → ℝ) (hne : core.Nonempty)
    (hsupport : ∀ color, color ∉ core → profile color = 0) :
    (∑ color, centerOnCore core profile color ^ 2) =
      (∑ color, profile color ^ 2) - (∑ color, profile color) ^ 2 / core.card := by
  have hcross (color : ι) : profile color * uniformFiniteProfile core color = profile color / core.card := by
    by_cases hc : color ∈ core <;> simp [uniformFiniteProfile, hc, hsupport, div_eq_mul_inv]
  have hrefsquare (color : ι) : uniformFiniteProfile core color ^ 2 = uniformFiniteProfile core color / core.card := by
    by_cases hc : color ∈ core <;> simp [uniformFiniteProfile, hc]
    ring
  unfold centerOnCore
  simp only [sub_sq, mul_pow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmiddle : (∑ color, 2 * profile color * (uniformFiniteProfile core color * ∑ x, profile x)) =
      2 * (∑ x, profile x) * ((∑ color, profile color) / core.card) := by
    simp_rw [show ∀ color, 2 * profile color * (uniformFiniteProfile core color * ∑ x, profile x) =
      (2 * ∑ x, profile x) * (profile color * uniformFiniteProfile core color) by intro; ring]
    rw [← Finset.mul_sum]
    simp only [hcross, ← Finset.sum_div]
  rw [hmiddle]
  simp only [hrefsquare, ← Finset.sum_mul, ← Finset.sum_div, uniformFiniteProfile_mass core hne]
  ring

theorem centerOnCore_square_le (core : Finset ι) (profile : ι → ℝ) (hne : core.Nonempty)
    (hsupport : ∀ color, color ∉ core → profile color = 0) :
    (∑ color, centerOnCore core profile color ^ 2) ≤ ∑ color, profile color ^ 2 := by
  rw [centerOnCore_square core profile hne hsupport]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

theorem coreSeed_eq_centers (core : Finset ι) (mass : ι → ι → ℝ) (first second : ι) :
    coreSeed core mass first second =
      centerOnCore core (fun x => centerOnCore core (restrictPair core mass x) second) first := by
  simp only [coreSeed, canonicalPair, centerOnCore, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x y => restrictPair core mass x y)]
  ring

/-- Restricting the true pair and canonicalizing on its core loses no
counting-L2 energy. No independent-product approximation is introduced. -/
theorem coreSeed_square_le (core : Finset ι) (mass : ι → ι → ℝ) (hne : core.Nonempty) :
    (∑ first, ∑ second, coreSeed core mass first second ^ 2) ≤ ∑ first, ∑ second, mass first second ^ 2 := by
  have hcolumn (second : ι) :
      (∑ first, coreSeed core mass first second ^ 2) ≤
        ∑ first, centerOnCore core (restrictPair core mass first) second ^ 2 := by
    simp_rw [coreSeed_eq_centers]
    apply centerOnCore_square_le core _ hne
    intro color hout
    simp [centerOnCore, restrictPair, hout]
  calc
    _ = ∑ second, ∑ first, coreSeed core mass first second ^ 2 := Finset.sum_comm
    _ ≤ ∑ second, ∑ first, centerOnCore core (restrictPair core mass first) second ^ 2 :=
      Finset.sum_le_sum fun second _ => hcolumn second
    _ = ∑ first, ∑ second, centerOnCore core (restrictPair core mass first) second ^ 2 := Finset.sum_comm
    _ ≤ ∑ first, ∑ second, restrictPair core mass first second ^ 2 := by
      apply Finset.sum_le_sum
      intro first _
      exact centerOnCore_square_le core _ hne (by intro color hout; simp [restrictPair, hout])
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      unfold restrictPair
      split_ifs <;> simp [sq_nonneg]

end AFT.SafePair

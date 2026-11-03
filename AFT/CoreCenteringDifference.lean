import AFT.CoreProjectionEnergy

/-! # Exact cost of changing the canonical core reference to the full palette -/

namespace AFT.SafePair

open scoped BigOperators
open SafeConvolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pairCountingL2 (mass : ι → ι → ℝ) : ℝ := countingL2 (fun color : ι × ι => mass color.1 color.2)

omit [DecidableEq ι] in
theorem pairCountingL2_add (first second : ι → ι → ℝ) :
    pairCountingL2 (first + second) ≤ pairCountingL2 first + pairCountingL2 second :=
  countingL2_add _ _

omit [DecidableEq ι] in
theorem pairCountingL2_neg (mass : ι → ι → ℝ) : pairCountingL2 (-mass) = pairCountingL2 mass := countingL2_neg _

omit [DecidableEq ι] in
theorem pairCountingL2_tensor (first second : ι → ℝ) :
    pairCountingL2 (fun x y => first x * second y) = countingL2 first * countingL2 second := by
  unfold pairCountingL2 countingL2
  rw [Fintype.sum_prod_type]
  simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]

theorem uniformFiniteProfile_square (core : Finset ι) (hne : core.Nonempty) :
    (∑ color, uniformFiniteProfile core color ^ 2) = 1 / (core.card : ℝ) := by
  have hp (color : ι) : uniformFiniteProfile core color ^ 2 = uniformFiniteProfile core color / core.card := by
    by_cases hc : color ∈ core <;> simp [uniformFiniteProfile, hc]
    ring
  simp only [hp, ← Finset.sum_div, uniformFiniteProfile_mass core hne]

/-- The full exact distance between the two actual uniform reference laws. -/
theorem uniformCore_difference_square (core : Finset ι) (hne : core.Nonempty) :
    (∑ color, (uniformFiniteProfile core color - 1 / (Fintype.card ι : ℝ)) ^ 2) =
      1 / (core.card : ℝ) - 1 / (Fintype.card ι : ℝ) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    have hh : 0 < Fintype.card ι := lt_of_lt_of_le (Finset.card_pos.mpr hne) (Finset.card_le_univ core)
    positivity
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [uniformFiniteProfile_square core hne]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, uniformFiniteProfile_mass core hne, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

omit [DecidableEq ι] in
/-- A bounded nonnegative subprobability marginal has counting energy at
most its actual height. -/
theorem nonnegative_countingL2_le (profile : ι → ℝ) (upper : ℝ) (hu : 0 ≤ upper)
    (hp : ∀ color, 0 ≤ profile color) (hb : ∀ color, profile color ≤ upper)
    (hmass : (∑ color, profile color) ≤ 1) : countingL2 profile ≤ Real.sqrt upper := by
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ color, upper * profile color := Finset.sum_le_sum fun color _ => by
      nlinarith [mul_le_mul_of_nonneg_right (hb color) (hp color)]
    _ = upper * ∑ color, profile color := by rw [Finset.mul_sum]
    _ ≤ upper := by nlinarith

omit [DecidableEq ι] in
/-- Changing the centering law is a sum of two explicit rank-one profiles,
which keeps the reference-change error separate from the pair edge loss. -/
theorem canonicalPair_reference_difference (firstReference secondReference : ι → ℝ)
    (mass : ι → ι → ℝ) (first second : ι) :
    canonicalPair firstReference mass first second - canonicalPair secondReference mass first second =
      -((firstReference first - secondReference first) *
        ((∑ x, mass x second) - (∑ x, ∑ y, mass x y) * firstReference second)) -
      (((∑ y, mass first y) - (∑ x, ∑ y, mass x y) * secondReference first) *
        (firstReference second - secondReference second)) := by
  unfold canonicalPair
  ring

omit [DecidableEq ι] in
/-- The reference change has a palette-independent Hilbert estimate in
terms of actual marginal heights, total mass, and the two reference laws. -/
theorem canonicalPair_reference_L2_le (firstReference secondReference : ι → ℝ)
    (mass : ι → ι → ℝ) (upper : ℝ) (hu : 0 ≤ upper)
    (hmass : ∀ first second, 0 ≤ mass first second)
    (htotal : (∑ first, ∑ second, mass first second) ≤ 1)
    (hrow : ∀ first, (∑ second, mass first second) ≤ upper)
    (hcolumn : ∀ second, (∑ first, mass first second) ≤ upper) :
    pairCountingL2 (canonicalPair firstReference mass - canonicalPair secondReference mass) ≤
      countingL2 (firstReference - secondReference) *
        (2 * Real.sqrt upper + countingL2 firstReference + countingL2 secondReference) := by
  let total := ∑ first, ∑ second, mass first second
  let row := fun first => ∑ second, mass first second
  let column := fun second => ∑ first, mass first second
  have ht0 : 0 ≤ total := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hmass _ _
  have hr := nonnegative_countingL2_le row upper hu
    (fun _ => Finset.sum_nonneg fun _ _ => hmass _ _) hrow htotal
  have hc := nonnegative_countingL2_le column upper hu
    (fun _ => Finset.sum_nonneg fun _ _ => hmass _ _) hcolumn (by dsimp only [column]; rw [Finset.sum_comm]; exact htotal)
  have hcenter (marginal reference : ι → ℝ) (hm : countingL2 marginal ≤ Real.sqrt upper) :
      countingL2 (marginal - total • reference) ≤ Real.sqrt upper + countingL2 reference := by
    change countingL2 (marginal + -(total • reference)) ≤ _
    have hh := countingL2_add marginal (-(total • reference))
    rw [countingL2_neg, countingL2_smul, abs_of_nonneg ht0] at hh
    have hm' := mul_le_mul_of_nonneg_right htotal (countingL2_nonneg reference)
    exact hh.trans (by dsimp only [total] at *; nlinarith)
  have hfirst := hcenter column firstReference hc
  have hsecond := hcenter row secondReference hr
  have heq : canonicalPair firstReference mass - canonicalPair secondReference mass =
      -(fun x y => (firstReference - secondReference) x * (column - total • firstReference) y) +
      -(fun x y => (row - total • secondReference) x * (firstReference - secondReference) y) := by
    funext first second
    exact canonicalPair_reference_difference firstReference secondReference mass first second
  rw [heq]
  calc
    _ ≤ pairCountingL2 (-(fun x y => (firstReference - secondReference) x * (column - total • firstReference) y)) +
      pairCountingL2 (-(fun x y => (row - total • secondReference) x * (firstReference - secondReference) y)) := pairCountingL2_add _ _
    _ = countingL2 (firstReference - secondReference) * countingL2 (column - total • firstReference) +
      countingL2 (row - total • secondReference) * countingL2 (firstReference - secondReference) := by
      rw [pairCountingL2_neg, pairCountingL2_neg, pairCountingL2_tensor, pairCountingL2_tensor]
    _ ≤ countingL2 (firstReference - secondReference) * (Real.sqrt upper + countingL2 firstReference) +
      (Real.sqrt upper + countingL2 secondReference) * countingL2 (firstReference - secondReference) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (countingL2_nonneg _))
        (mul_le_mul_of_nonneg_right hsecond (countingL2_nonneg _))
    _ = _ := by ring

end AFT.SafePair

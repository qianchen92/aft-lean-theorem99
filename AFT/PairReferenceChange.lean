import AFT.CoreCenteringDifference

/-! # Literal rank-two correction between pair centering references -/

namespace AFT.SafePair

open scoped BigOperators
open SafeConvolution

variable {ι : Type*} [Fintype ι]

theorem canonicalPair_reference_l1_le (firstReference secondReference : FiniteDist ι)
    (mass : ι → ι → ℝ) (hmass : ∀ x y, 0 ≤ mass x y)
    (htotal : (∑ x, ∑ y, mass x y) = 1) :
    (∑ x, ∑ y, |canonicalPair firstReference.weight mass x y - canonicalPair secondReference.weight mass x y|) ≤
      4 * ∑ x, |firstReference.weight x - secondReference.weight x| := by
  have hrow (x : ι) : 0 ≤ ∑ y, mass x y := Finset.sum_nonneg fun _ _ => hmass _ _
  have hcol (y : ι) : 0 ≤ ∑ x, mass x y := Finset.sum_nonneg fun _ _ => hmass _ _
  have hpoint (x y : ι) : |canonicalPair firstReference.weight mass x y - canonicalPair secondReference.weight mass x y| ≤
      |firstReference.weight x - secondReference.weight x| * ((∑ a, mass a y) + firstReference.weight y) +
      ((∑ b, mass x b) + secondReference.weight x) * |firstReference.weight y - secondReference.weight y| := by
    rw [canonicalPair_reference_difference, htotal, one_mul, one_mul]
    apply (abs_sub _ _).trans
    simp only [abs_neg, abs_mul]
    have hc := abs_sub (∑ a, mass a y) (firstReference.weight y)
    have hr := abs_sub (∑ b, mass x b) (secondReference.weight x)
    rw [abs_of_nonneg (hcol y), abs_of_nonneg (firstReference.nonneg y)] at hc
    rw [abs_of_nonneg (hrow x), abs_of_nonneg (secondReference.nonneg x)] at hr
    exact add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hr (abs_nonneg _))
  calc
    _ ≤ ∑ x, ∑ y, (|firstReference.weight x - secondReference.weight x| *
        ((∑ a, mass a y) + firstReference.weight y) +
        ((∑ b, mass x b) + secondReference.weight x) * |firstReference.weight y - secondReference.weight y|) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpoint x y
    _ = 4 * ∑ x, |firstReference.weight x - secondReference.weight x| := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [Finset.sum_comm (f := fun y a => mass a y), htotal, firstReference.sum_one, secondReference.sum_one]
      ring

/-- The pointwise cost of changing centering references keeps both
endpoint marginals and both genuine probability references. -/
theorem canonicalPair_reference_point_le (firstReference secondReference : FiniteDist ι)
    (mass : ι → ι → ℝ) (hmass : ∀ x y, 0 ≤ mass x y)
    (htotal : (∑ x, ∑ y, mass x y) = 1) (upper : ℝ)
    (hfirst : ∀ x, firstReference.weight x ≤ upper) (hsecond : ∀ x, secondReference.weight x ≤ upper)
    (hrow : ∀ x, (∑ y, mass x y) ≤ upper) (hcolumn : ∀ y, (∑ x, mass x y) ≤ upper)
    (x y : ι) : |canonicalPair firstReference.weight mass x y - canonicalPair secondReference.weight mass x y| ≤ 2 * upper ^ 2 := by
  have hu : 0 ≤ upper := (firstReference.nonneg x).trans (hfirst x)
  have hdelta (a : ι) : |firstReference.weight a - secondReference.weight a| ≤ upper :=
    abs_le.mpr ⟨by linarith [firstReference.nonneg a, hsecond a], by linarith [secondReference.nonneg a, hfirst a]⟩
  have hc : |(∑ a, mass a y) - firstReference.weight y| ≤ upper :=
    abs_le.mpr ⟨by linarith [Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => hmass a y), hfirst y],
      by linarith [firstReference.nonneg y, hcolumn y]⟩
  have hr : |(∑ b, mass x b) - secondReference.weight x| ≤ upper :=
    abs_le.mpr ⟨by linarith [Finset.sum_nonneg (fun b (_ : b ∈ Finset.univ) => hmass x b), hsecond x],
      by linarith [secondReference.nonneg x, hrow x]⟩
  rw [canonicalPair_reference_difference, htotal, one_mul, one_mul]
  apply (abs_sub _ _).trans
  simp only [abs_neg, abs_mul]
  exact (add_le_add (mul_le_mul (hdelta x) hc (abs_nonneg _) hu)
    (mul_le_mul hr (hdelta y) (abs_nonneg _) hu)).trans_eq (by ring)

/-- The reference correction has full squared energy proportional to the
actual reference L1 difference, rather than to the palette dimension. -/
theorem canonicalPair_reference_square_le (firstReference secondReference : FiniteDist ι)
    (mass : ι → ι → ℝ) (hmass : ∀ x y, 0 ≤ mass x y)
    (htotal : (∑ x, ∑ y, mass x y) = 1) (upper : ℝ) (_hu : 0 ≤ upper)
    (hfirst : ∀ x, firstReference.weight x ≤ upper) (hsecond : ∀ x, secondReference.weight x ≤ upper)
    (hrow : ∀ x, (∑ y, mass x y) ≤ upper) (hcolumn : ∀ y, (∑ x, mass x y) ≤ upper) :
    (∑ x, ∑ y, (canonicalPair firstReference.weight mass x y - canonicalPair secondReference.weight mass x y)^2) ≤
      8 * upper ^ 2 * ∑ x, |firstReference.weight x - secondReference.weight x| := by
  calc
    _ ≤ ∑ x, ∑ y, (2 * upper ^ 2) *
        |canonicalPair firstReference.weight mass x y - canonicalPair secondReference.weight mass x y| := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hp := mul_le_mul_of_nonneg_right
        (canonicalPair_reference_point_le firstReference secondReference mass hmass htotal upper hfirst hsecond hrow hcolumn x y)
        (abs_nonneg (canonicalPair firstReference.weight mass x y - canonicalPair secondReference.weight mass x y))
      simpa only [← sq, sq_abs] using hp
    _ = (2 * upper ^ 2) * ∑ x, ∑ y,
        |canonicalPair firstReference.weight mass x y - canonicalPair secondReference.weight mass x y| := by
      simp only [Finset.mul_sum]
    _ ≤ (2 * upper ^ 2) * (4 * ∑ x, |firstReference.weight x - secondReference.weight x|) :=
      mul_le_mul_of_nonneg_left (canonicalPair_reference_l1_le firstReference secondReference mass hmass htotal) (by positivity)
    _ = _ := by ring

end AFT.SafePair

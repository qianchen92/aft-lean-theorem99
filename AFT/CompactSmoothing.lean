import AFT.FiniteConvolution
import AFT.TrimmedSlice
import AFT.Charge

/-!
# Actual compact interval smoothing and its source-translation defect
-/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

noncomputable def pushIntegerKernel (embedding : ℤ →+ G) (support : Finset ℤ)
    (kernel : ℤ → ℝ) (color : G) : ℝ :=
  ∑ offset ∈ support, if embedding offset = color then kernel offset else 0

noncomputable def intervalKernel (embedding : ℤ →+ G) (start : ℤ) (width : ℕ) : G → ℝ :=
  pushIntegerKernel embedding (anchorInterval start width) (intervalAnchorLaw start width)

theorem pushIntegerKernel_L1_le (embedding : ℤ →+ G) (support : Finset ℤ) (kernel : ℤ → ℝ) :
    kernelL1 (pushIntegerKernel embedding support kernel) ≤ ∑ offset ∈ support, |kernel offset| := by
  unfold kernelL1 pushIntegerKernel
  calc
    _ ≤ ∑ color : G, ∑ offset ∈ support, |if embedding offset = color then kernel offset else 0| :=
      Finset.sum_le_sum fun color _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro offset _
      simp only [apply_ite abs, abs_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [Fintype G] in
theorem intervalKernel_nonneg (embedding : ℤ →+ G) (start : ℤ) (width : ℕ) (color : G) :
    0 ≤ intervalKernel embedding start width color := by
  unfold intervalKernel pushIntegerKernel
  apply Finset.sum_nonneg
  intro offset _
  split_ifs
  · exact intervalAnchorLaw_nonneg _ _ _
  · rfl

theorem intervalKernel_mass (embedding : ℤ →+ G) (start : ℤ) (width : ℕ) (hw : width ≠ 0) :
    (∑ color, intervalKernel embedding start width color) = 1 := by
  unfold intervalKernel pushIntegerKernel
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact intervalAnchorLaw_mass start width hw

noncomputable def intervalDistribution (embedding : ℤ →+ G) (start : ℤ) (width : ℕ) (hw : width ≠ 0) :
    FiniteDist G where
  weight := intervalKernel embedding start width
  nonneg := intervalKernel_nonneg embedding start width
  sum_one := intervalKernel_mass embedding start width hw

omit [Fintype G] in
/-- Pushing a shifted integer interval into the palette commutes exactly
with palette translation, including before imposing no-wrap margins. -/
theorem intervalKernel_translate (embedding : ℤ →+ G) (start shift : ℤ) (width : ℕ) (color : G) :
    intervalKernel embedding (start + shift) width color =
      intervalKernel embedding start width (color - embedding shift) := by
  unfold intervalKernel pushIntegerKernel
  apply Finset.sum_bij (fun offset _ => offset - shift)
  · intro offset ho
    simp only [anchorInterval, Finset.mem_Ico] at ho ⊢
    omega
  · intro a _ b _ heq
    omega
  · intro offset ho
    refine ⟨offset + shift, ?_, by omega⟩
    simp only [anchorInterval, Finset.mem_Ico] at ho ⊢
    omega
  · intro offset _
    have heq : embedding offset = color ↔ embedding (offset - shift) = color - embedding shift := by
      rw [map_sub]
      exact sub_left_inj.symm
    simp only [heq, intervalAnchorLaw_translate]

/-- The sharp interval L1 translation estimate survives pushforward to
any finite abelian palette, without an injectivity requirement. -/
theorem intervalKernel_translation_L1_le (embedding : ℤ →+ G) (start shift : ℤ) (width : ℕ) :
    kernelL1 (intervalKernel embedding (start + shift) width - intervalKernel embedding start width) ≤
      2 * (shift.natAbs : ℝ) / width := by
  let support := anchorInterval start width ∪ anchorInterval (start + shift) width
  have hfirst (color : G) : intervalKernel embedding start width color =
      pushIntegerKernel embedding support (intervalAnchorLaw start width) color := by
    unfold intervalKernel pushIntegerKernel
    apply Finset.sum_subset Finset.subset_union_left
    intro offset _ hout
    simp [intervalAnchorLaw, hout]
  have hsecond (color : G) : intervalKernel embedding (start + shift) width color =
      pushIntegerKernel embedding support (intervalAnchorLaw (start + shift) width) color := by
    unfold intervalKernel pushIntegerKernel
    apply Finset.sum_subset Finset.subset_union_right
    intro offset _ hout
    simp [intervalAnchorLaw, hout]
  have heq : intervalKernel embedding (start + shift) width - intervalKernel embedding start width =
      pushIntegerKernel embedding support (fun offset => intervalAnchorLaw (start + shift) width offset -
        intervalAnchorLaw start width offset) := by
    funext color
    simp only [Pi.sub_apply, hfirst, hsecond, pushIntegerKernel, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro offset _
    split_ifs <;> simp
  rw [heq]
  have hh := pushIntegerKernel_L1_le embedding support (fun offset =>
    intervalAnchorLaw (start + shift) width offset - intervalAnchorLaw start width offset)
  rw [TrimmedSlice.interval_translation_l1] at hh
  exact hh.trans (div_le_div_of_nonneg_right (by
    have hm : (min width shift.natAbs : ℝ) ≤ shift.natAbs := by exact_mod_cast min_le_right width shift.natAbs
    linarith) (Nat.cast_nonneg width))

noncomputable def translateDistribution (source : FiniteDist G) (shift : G) : FiniteDist G where
  weight color := source.weight (color - shift)
  nonneg color := source.nonneg _
  sum_one := by rw [translated_sum, source.sum_one]

omit [DecidableEq G] in
/-- The two-coordinate product defect is the sum of its coordinate costs. -/
theorem product_translation_L1_le (first second : FiniteDist G) (firstShift secondShift : G) :
    kernelL1 (fun point : G × G =>
      first.weight (point.1 - firstShift) * second.weight (point.2 - secondShift) - first.weight point.1 * second.weight point.2) ≤
      kernelL1 (fun color => first.weight (color - firstShift) - first.weight color) +
      kernelL1 (fun color => second.weight (color - secondShift) - second.weight color) := by
  have hpoint (x y : G) :
      |first.weight (x - firstShift) * second.weight (y - secondShift) - first.weight x * second.weight y| ≤
      |first.weight (x - firstShift) - first.weight x| * second.weight (y - secondShift) +
        first.weight x * |second.weight (y - secondShift) - second.weight y| := by
    have heq : first.weight (x - firstShift) * second.weight (y - secondShift) - first.weight x * second.weight y =
        (first.weight (x - firstShift) - first.weight x) * second.weight (y - secondShift) +
        first.weight x * (second.weight (y - secondShift) - second.weight y) := by ring
    rw [heq]
    simpa only [abs_mul, abs_of_nonneg (first.nonneg _), abs_of_nonneg (second.nonneg _)] using abs_add_le
      ((first.weight (x - firstShift) - first.weight x) * second.weight (y - secondShift))
      (first.weight x * (second.weight (y - secondShift) - second.weight y))
  unfold kernelL1
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ x, ∑ y, (|first.weight (x - firstShift) - first.weight x| * second.weight (y - secondShift) +
        first.weight x * |second.weight (y - secondShift) - second.weight y|) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpoint x y
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, translated_sum, second.sum_one, mul_one]
      rw [← Finset.sum_mul, first.sum_one, one_mul]

theorem box_translation_L1_le (embedding : ℤ →+ G) (start firstShift secondShift : ℤ)
    (width : ℕ) (hw : width ≠ 0) :
    kernelL1 (fun point : G × G =>
      intervalKernel embedding start width (point.1 - embedding firstShift) *
        intervalKernel embedding start width (point.2 - embedding secondShift) -
      intervalKernel embedding start width point.1 * intervalKernel embedding start width point.2) ≤
      2 * ((firstShift.natAbs : ℝ) + secondShift.natAbs) / width := by
  have hh := product_translation_L1_le (intervalDistribution embedding start width hw)
    (intervalDistribution embedding start width hw) (embedding firstShift) (embedding secondShift)
  change _ ≤ kernelL1 (fun color => intervalKernel embedding start width (color - embedding firstShift) - intervalKernel embedding start width color) +
    kernelL1 (fun color => intervalKernel embedding start width (color - embedding secondShift) - intervalKernel embedding start width color) at hh
  simp_rw [← intervalKernel_translate] at hh
  have h1 := intervalKernel_translation_L1_le embedding start firstShift width
  have h2 := intervalKernel_translation_L1_le embedding start secondShift width
  exact (hh.trans (add_le_add h1 h2)).trans_eq (by ring)

end AFT.SafeConvolution

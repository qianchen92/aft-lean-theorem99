import AFT.MixedKernel

/-! # Tensor multiplication of the full mixed input activity -/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Left Right Color : Type*} [Fintype Left] [Fintype Right] [Fintype Color]
  [DecidableEq Left] [DecidableEq Right]

def tensor (first : (Left → Color) → ℝ) (second : (Right → Color) → ℝ) :
    ((Left ⊕ Right) → Color) → ℝ :=
  fun word => first (word ∘ Sum.inl) * second (word ∘ Sum.inr)

omit [Fintype Left] [Fintype Right] [Fintype Color] in
@[simp] theorem freeze_disjSum_left (first : Finset Left) (second : Finset Right)
    (values integrated : Left ⊕ Right → Color) :
    freeze (first.disjSum second) values integrated ∘ Sum.inl =
      freeze first (values ∘ Sum.inl) (integrated ∘ Sum.inl) := by
  ext slot
  simp [freeze]

omit [Fintype Left] [Fintype Right] [Fintype Color] in
@[simp] theorem freeze_disjSum_right (first : Finset Left) (second : Finset Right)
    (values integrated : Left ⊕ Right → Color) :
    freeze (first.disjSum second) values integrated ∘ Sum.inr =
      freeze second (values ∘ Sum.inr) (integrated ∘ Sum.inr) := by
  ext slot
  simp [freeze]

/-- Every tensor-product fiber factors exactly, with arbitrary joint
kernels in its two disjoint groups of arguments. -/
theorem fiberSq_tensor (p : Left → FiniteDist Color) (q : Right → FiniteDist Color)
    (first : (Left → Color) → ℝ) (second : (Right → Color) → ℝ)
    (S : Finset Left) (T : Finset Right) (values : Left ⊕ Right → Color) :
    fiberSq (Sum.elim p q) (tensor first second) (S.disjSum T) values =
      fiberSq p first S (values ∘ Sum.inl) * fiberSq q second T (values ∘ Sum.inr) := by
  simp only [fiberSq, FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.independent,
    tensor, freeze_disjSum_left, freeze_disjSum_right, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  let f : (Left → Color) → ℝ := fun integrated => (∏ i, (p i).weight (integrated i)) *
    first (freeze S (values ∘ Sum.inl) integrated) ^ 2
  let g : (Right → Color) → ℝ := fun integrated => (∏ i, (q i).weight (integrated i)) *
    second (freeze T (values ∘ Sum.inr) integrated) ^ 2
  have h := (Equiv.sumArrowEquivProdArrow Left Right Color).sum_comp (fun pair => f pair.1 * g pair.2)
  calc
    _ = ∑ pair : (Left → Color) × (Right → Color), f pair.1 * g pair.2 := by
      convert h using 1
      apply Finset.sum_congr rfl
      intro word _
      dsimp [f, g, Equiv.sumArrowEquivProdArrow]
      ring
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Supremizing over fixed values gives the required dimension-free
multiplicative estimate. -/
theorem fiberNorm_tensor_le (p : Left → FiniteDist Color) (q : Right → FiniteDist Color)
    (first : (Left → Color) → ℝ) (second : (Right → Color) → ℝ)
    (S : Finset Left) (T : Finset Right) :
    fiberNorm (Sum.elim p q) (tensor first second) (S.disjSum T) ≤
      fiberNorm p first S * fiberNorm q second T := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (fiberNorm_nonneg p first S) (fiberNorm_nonneg q second T))).mpr
  intro values
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), fiberSq_tensor,
    Real.sqrt_mul (fiberSq_nonneg p first S _)]
  have hf := norm_le_pi_norm (fun values => Real.sqrt (fiberSq p first S values)) (values ∘ Sum.inl)
  have hg := norm_le_pi_norm (fun values => Real.sqrt (fiberSq q second T values)) (values ∘ Sum.inr)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hf hg
  exact mul_le_mul hf hg (Real.sqrt_nonneg _) (fiberNorm_nonneg p first S)

/-- All fixed-coordinate sets are included in this product bound. Thus it
applies to unequal primary/body pool sizes as well as to pure kernels. -/
theorem activity_tensor_le (leftRate : Left → ℝ) (rightRate : Right → ℝ)
    (p : Left → FiniteDist Color) (q : Right → FiniteDist Color)
    (first : (Left → Color) → ℝ) (second : (Right → Color) → ℝ)
    (hl : ∀ i, 0 ≤ leftRate i) (hr : ∀ i, 0 ≤ rightRate i) :
    activity (Sum.elim leftRate rightRate) (Sum.elim p q) (tensor first second) ≤
      activity leftRate p first * activity rightRate q second := by
  let term : Finset (Left ⊕ Right) → ℝ := fun fixed =>
    (∏ i ∈ fixed, Sum.elim leftRate rightRate i) * fiberNorm (Sum.elim p q) (tensor first second) fixed
  have hreindex := (Finset.sumEquiv (α := Left) (β := Right)).toEquiv.symm.sum_comp term
  change (∏ i, Sum.elim leftRate rightRate i) * (∑ fixed, term fixed) ≤ _
  rw [← hreindex, Fintype.sum_prod_type]
  have hsum : (∑ S : Finset Left, ∑ T : Finset Right, term (S.disjSum T)) ≤
      (∑ S : Finset Left, (∏ i ∈ S, leftRate i) * fiberNorm p first S) *
        (∑ T : Finset Right, (∏ i ∈ T, rightRate i) * fiberNorm q second T) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_le_sum
    intro S _
    apply Finset.sum_le_sum
    intro T _
    dsimp [term]
    rw [Finset.prod_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h := mul_le_mul_of_nonneg_left (a := (∏ i ∈ S, leftRate i) * ∏ i ∈ T, rightRate i) (fiberNorm_tensor_le p q first second S T)
      (mul_nonneg (Finset.prod_nonneg fun i _ => hl i) (Finset.prod_nonneg fun i _ => hr i))
    convert h using 1
    ring
  have h := mul_le_mul_of_nonneg_left (a := (∏ i, leftRate i) * ∏ i, rightRate i) hsum
    (mul_nonneg (Finset.prod_nonneg fun i _ => hl i) (Finset.prod_nonneg fun i _ => hr i))
  simpa only [Finset.sumEquiv_symm_apply, Fintype.prod_sum_type, Sum.elim_inl,
    Sum.elim_inr, activity, mul_mul_mul_comm] using h

end

end AFT.MixedKernel

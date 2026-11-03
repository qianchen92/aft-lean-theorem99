import AFT.MixedKernel

/-! # The four actual fibers of a two-coordinate input kernel -/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

def pairReference (first second : FiniteDist Color) : Fin 2 → FiniteDist Color := ![first, second]

def pairKernel (kernel : Color → Color → ℝ) (word : Fin 2 → Color) : ℝ := kernel (word 0) (word 1)

theorem pair_expectation (first second : FiniteDist Color) (kernel : Color → Color → ℝ) :
    (FiniteDist.independent (pairReference first second)).expectation (pairKernel kernel) =
      ∑ x, ∑ y, first.weight x * second.weight y * kernel x y := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← Equiv.sum_comp (finTwoArrowEquiv Color).symm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp [pairReference, pairKernel, Fin.prod_univ_two, finTwoArrowEquiv]

theorem pair_fiberSq (first second : FiniteDist Color) (kernel : Color → Color → ℝ)
    (fixed : Finset (Fin 2)) (values : Fin 2 → Color) :
    fiberSq (pairReference first second) (pairKernel kernel) fixed values =
      ∑ x, ∑ y, first.weight x * second.weight y *
        kernel (if 0 ∈ fixed then values 0 else x) (if 1 ∈ fixed then values 1 else y) ^ 2 := by
  exact pair_expectation first second (fun x y =>
    kernel (if 0 ∈ fixed then values 0 else x) (if 1 ∈ fixed then values 1 else y) ^ 2)

theorem pair_fiberSq_empty (first second : FiniteDist Color) (kernel : Color → Color → ℝ)
    (values : Fin 2 → Color) :
    fiberSq (pairReference first second) (pairKernel kernel) ∅ values =
      ∑ x, ∑ y, first.weight x * second.weight y * kernel x y ^ 2 := by
  rw [pair_fiberSq]
  simp only [Finset.notMem_empty, if_false]

theorem pair_fiberSq_first (first second : FiniteDist Color) (kernel : Color → Color → ℝ)
    (values : Fin 2 → Color) :
    fiberSq (pairReference first second) (pairKernel kernel) {0} values =
      ∑ y, second.weight y * kernel (values 0) y ^ 2 := by
  rw [pair_fiberSq]
  simp only [Finset.mem_singleton, ↓reduceIte, (by decide : (1 : Fin 2) ≠ 0)]
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, first.sum_one, one_mul]

theorem pair_fiberSq_second (first second : FiniteDist Color) (kernel : Color → Color → ℝ)
    (values : Fin 2 → Color) :
    fiberSq (pairReference first second) (pairKernel kernel) {1} values =
      ∑ x, first.weight x * kernel x (values 1) ^ 2 := by
  rw [pair_fiberSq]
  simp only [Finset.mem_singleton, ↓reduceIte, Fin.zero_ne_one]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, second.sum_one, mul_one]

theorem pair_fiberSq_both (first second : FiniteDist Color) (kernel : Color → Color → ℝ)
    (values : Fin 2 → Color) :
    fiberSq (pairReference first second) (pairKernel kernel) {0, 1} values = kernel (values 0) (values 1) ^ 2 := by
  rw [pair_fiberSq]
  simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, ↓reduceIte,
    ← Finset.sum_mul, ← Finset.mul_sum, first.sum_one, second.sum_one, mul_one, one_mul]

theorem pair_activity_formula (first second : FiniteDist Color) (kernel : Color → Color → ℝ)
    (firstRate secondRate : ℝ) :
    activity ![firstRate, secondRate] (pairReference first second) (pairKernel kernel) =
      firstRate * secondRate * (fiberNorm (pairReference first second) (pairKernel kernel) ∅ +
        firstRate * fiberNorm (pairReference first second) (pairKernel kernel) {0} +
        secondRate * fiberNorm (pairReference first second) (pairKernel kernel) {1} +
        (firstRate * secondRate) * fiberNorm (pairReference first second) (pairKernel kernel) {0, 1}) := by
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have hprod : (∏ slot ∈ ({0, 1} : Finset (Fin 2)), ![firstRate, secondRate] slot) = firstRate * secondRate := by
    rw [Finset.prod_pair (by decide : (0 : Fin 2) ≠ (1 : Fin 2))]
    rfl
  unfold activity
  rw [hu]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.prod_empty, Finset.prod_singleton, hprod, one_mul]
  ring

theorem pair_fiberNorm_le (first second : FiniteDist Color) (kernel : Color → Color → ℝ)
    (fixed : Finset (Fin 2)) (bound : ℝ) (hbound : 0 ≤ bound)
    (h : ∀ values, fiberSq (pairReference first second) (pairKernel kernel) fixed values ≤ bound ^ 2) :
    fiberNorm (pairReference first second) (pairKernel kernel) fixed ≤ bound := by
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  intro values
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_left hbound).mpr (h values)

/-- Full L2, fixed-first, fixed-second, and pointwise estimates imply the
literal mixed activity, with the two population rates kept separate. -/
theorem pair_activity_le (first second : FiniteDist Color) (kernel : Color → Color → ℝ)
    (firstRate secondRate full firstFixed secondFixed both : ℝ)
    (hfirstRate : 0 ≤ firstRate) (hsecondRate : 0 ≤ secondRate)
    (hfull : 0 ≤ full) (hfirst : 0 ≤ firstFixed) (hsecond : 0 ≤ secondFixed) (hboth : 0 ≤ both)
    (hfullSq : (∑ x, ∑ y, first.weight x * second.weight y * kernel x y ^ 2) ≤ full ^ 2)
    (hfirstSq : ∀ x, (∑ y, second.weight y * kernel x y ^ 2) ≤ firstFixed ^ 2)
    (hsecondSq : ∀ y, (∑ x, first.weight x * kernel x y ^ 2) ≤ secondFixed ^ 2)
    (hpoint : ∀ x y, |kernel x y| ≤ both) :
    activity ![firstRate, secondRate] (pairReference first second) (pairKernel kernel) ≤
      firstRate * secondRate * (full + firstRate * firstFixed + secondRate * secondFixed +
        firstRate * secondRate * both) := by
  rw [pair_activity_formula]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hfirstRate hsecondRate)
  have hf := pair_fiberNorm_le first second kernel ∅ full hfull (fun values => by rw [pair_fiberSq_empty]; exact hfullSq)
  have h1 := pair_fiberNorm_le first second kernel {0} firstFixed hfirst (fun values => by rw [pair_fiberSq_first]; exact hfirstSq _)
  have h2 := pair_fiberNorm_le first second kernel {1} secondFixed hsecond (fun values => by rw [pair_fiberSq_second]; exact hsecondSq _)
  have hb := pair_fiberNorm_le first second kernel {0, 1} both hboth (fun values => by
    rw [pair_fiberSq_both]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hboth).mpr (hpoint _ _))
  exact add_le_add (add_le_add (add_le_add hf (mul_le_mul_of_nonneg_left h1 hfirstRate))
    (mul_le_mul_of_nonneg_left h2 hsecondRate))
    (mul_le_mul_of_nonneg_left hb (mul_nonneg hfirstRate hsecondRate))

end

end AFT.MixedKernel

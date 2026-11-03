import AFT.MixedKernel

/-! # Full mixed activity from integrated, one-fixed, and sup fibers -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [DecidableEq Slot]

theorem fiberSq_le_sup_square (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hkernel : ∀ word, |kernel word| ≤ bound) (fixed : Finset Slot) (values : Slot → Color) :
    fiberSq reference kernel fixed values ≤ bound ^ 2 := by
  have hpoint (word) : kernel (freeze fixed values word) ^ 2 ≤ bound ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hbound).mpr (hkernel (freeze fixed values word))
  change (∑ word, (FiniteDist.independent reference).weight word * kernel (freeze fixed values word) ^ 2) ≤ _
  calc
    _ ≤ ∑ word, (FiniteDist.independent reference).weight word * bound ^ 2 :=
      Finset.sum_le_sum fun word _ => mul_le_mul_of_nonneg_left (hpoint word) ((FiniteDist.independent reference).nonneg word)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem fiberNorm_le_square_bound (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (bound : ℝ) (hbound : 0 ≤ bound)
    (hkernel : ∀ values, fiberSq reference kernel fixed values ≤ bound ^ 2) :
    fiberNorm reference kernel fixed ≤ bound := by
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  intro values
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_iff.mpr ⟨hbound, hkernel values⟩

theorem fiberNorm_le_sup (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hkernel : ∀ word, |kernel word| ≤ bound) (fixed : Finset Slot) :
    fiberNorm reference kernel fixed ≤ bound :=
  fiberNorm_le_square_bound reference kernel fixed bound hbound
    (fiberSq_le_sup_square reference kernel bound hbound hkernel fixed)

/-- The extra penalty of a second fixed output absorbs the stronger sup
bound. No minimum atom probability is introduced. -/
theorem activity_le_three_fibers (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (rate full oneFixed sup : ℝ)
    (hrate : 0 ≤ rate) (hrate1 : rate ≤ 1)
    (hfull : 0 ≤ full) (hone : 0 ≤ oneFixed) (hsup : 0 ≤ sup)
    (hfullSq : (FiniteDist.independent reference).l2Sq kernel ≤ full ^ 2)
    (honeSq : ∀ slot values, fiberSq reference kernel {slot} values ≤ oneFixed ^ 2)
    (hsupPoint : ∀ word, |kernel word| ≤ sup) :
    activity (fun _ : Slot => rate) reference kernel ≤
      (2 : ℝ) ^ Fintype.card Slot * rate ^ Fintype.card Slot *
        (full + rate * oneFixed + rate ^ 2 * sup) := by
  have hF : fiberNorm reference kernel ∅ ≤ full := by
    rw [fiberNorm_empty]
    exact Real.sqrt_le_iff.mpr ⟨hfull,hfullSq⟩
  have hG (slot) : fiberNorm reference kernel {slot} ≤ oneFixed :=
    fiberNorm_le_square_bound reference kernel {slot} oneFixed hone (honeSq slot)
  have hH (fixed) : fiberNorm reference kernel fixed ≤ sup :=
    fiberNorm_le_sup reference kernel sup hsup hsupPoint fixed
  have hterm (fixed : Finset Slot) :
      (∏ slot ∈ fixed, rate) * fiberNorm reference kernel fixed ≤
        full + rate * oneFixed + rate ^ 2 * sup := by
    simp only [Finset.prod_const]
    by_cases hz : fixed.card = 0
    · have he := Finset.card_eq_zero.mp hz
      subst fixed
      simpa only [Finset.card_empty,pow_zero,one_mul] using
        hF.trans (by nlinarith [mul_nonneg hrate hone,mul_nonneg (sq_nonneg rate) hsup])
    · by_cases ho : fixed.card = 1
      · obtain ⟨slot,rfl⟩ := Finset.card_eq_one.mp ho
        simpa only [Finset.card_singleton,pow_one] using
          (mul_le_mul_of_nonneg_left (hG slot) hrate).trans
            (by nlinarith [mul_nonneg (sq_nonneg rate) hsup])
      · have hn : 2 ≤ fixed.card := by omega
        have hp : rate ^ fixed.card ≤ rate ^ 2 := pow_le_pow_of_le_one hrate hrate1 hn
        have hh := mul_le_mul hp (hH fixed) (fiberNorm_nonneg reference kernel fixed) (sq_nonneg rate)
        exact hh.trans (by nlinarith [mul_nonneg hrate hone])
  unfold activity
  simp only [Finset.prod_const, Finset.card_univ]
  calc
    _ ≤ rate ^ Fintype.card Slot *
        ∑ _fixed : Finset Slot, (full + rate * oneFixed + rate ^ 2 * sup) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun fixed _ => by
        simpa only [Finset.prod_const] using hterm fixed) (pow_nonneg hrate _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

end
end AFT.MixedKernel

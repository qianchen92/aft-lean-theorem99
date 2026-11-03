import AFT.JointBoundaryProjection

/-! # Changing fixed-coordinate laws preserves the full mixed-fiber bound -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- Freezing an independent word at independently drawn values gives the
coordinatewise mixture of the two laws, exactly. -/
theorem expectation_freeze_laws (reference alternate : Slot → FiniteDist Color)
    (fixed : Finset Slot) (kernel : (Slot → Color) → ℝ) :
    (FiniteDist.independent alternate).expectation (fun values =>
      (FiniteDist.independent reference).expectation (fun word => kernel (freeze fixed values word))) =
    (FiniteDist.independent (fun slot => if slot ∈ fixed then alternate slot else reference slot)).expectation kernel := by
  let first : ((Slot → Color) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun f => (FiniteDist.independent alternate).expectation (fun values =>
      (FiniteDist.independent reference).expectation (fun word => f (freeze fixed values word)))
    map_add' := by intros; simp only [Pi.add_apply, FiniteDist.expectation_add]
    map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, FiniteDist.expectation_const_mul, RingHom.id_apply] }
  let second : ((Slot → Color) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := (FiniteDist.independent (fun slot => if slot ∈ fixed then alternate slot else reference slot)).expectation
    map_add' := fun f g => FiniteDist.expectation_add _ f g
    map_smul' := fun scalar f => FiniteDist.expectation_const_mul _ scalar f }
  have hp (functions : Slot → Color → ℝ) : first (productKernel functions) = second (productKernel functions) := by
    change (FiniteDist.independent alternate).expectation (fun values =>
      (FiniteDist.independent reference).expectation (productKernel (fun slot color =>
        functions slot (if slot ∈ fixed then values slot else color)))) = _
    simp_rw [expectation_productKernel]
    have he (values) : (∏ slot, (reference slot).expectation (fun color =>
        functions slot (if slot ∈ fixed then values slot else color))) =
        productKernel (fun slot color => if slot ∈ fixed then functions slot color else
          (reference slot).expectation (functions slot)) values := by
      apply Finset.prod_congr rfl
      intro slot _
      by_cases hs : slot ∈ fixed <;> simp [hs, FiniteDist.expectation_const]
    simp_rw [he]
    rw [expectation_productKernel]
    change _ = (FiniteDist.independent _).expectation (productKernel functions)
    rw [expectation_productKernel]
    apply Finset.prod_congr rfl
    intro slot _
    by_cases hs : slot ∈ fixed <;> simp [hs, FiniteDist.expectation_const]
  change first kernel = second kernel
  rw [kernel_product_expansion kernel]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro point _
  exact congrArg (kernel point * ·) (hp _)

/-- Any replacement of the fixed coordinate laws is bounded by the
original fixed-coordinate Hilbert supremum. -/
theorem l2Sq_le_fiberNorm_of_eq_off_fixed (reference alternate : Slot → FiniteDist Color)
    (fixed : Finset Slot) (hequal : ∀ slot ∉ fixed, alternate slot = reference slot)
    (kernel : (Slot → Color) → ℝ) :
    (FiniteDist.independent alternate).l2Sq kernel ≤ fiberNorm reference kernel fixed ^ 2 := by
  have hlaw : (fun slot => if slot ∈ fixed then alternate slot else reference slot) = alternate := by
    funext slot
    split_ifs with hs
    · rfl
    · exact (hequal slot hs).symm
  have he := expectation_freeze_laws reference alternate fixed (fun word => kernel word ^ 2)
  rw [hlaw] at he
  change (FiniteDist.independent alternate).expectation (fun word => kernel word ^ 2) ≤ _
  rw [← he]
  calc
    _ ≤ (FiniteDist.independent alternate).expectation (fun _ => fiberNorm reference kernel fixed ^ 2) := by
      apply Finset.sum_le_sum
      intro values _
      exact mul_le_mul_of_nonneg_left (fiberSq_le_norm_sq reference kernel fixed values)
        ((FiniteDist.independent alternate).nonneg values)
    _ = _ := FiniteDist.expectation_const _ _

/-- Arbitrary positive finite weights on fixed slots incur only their total
masses, and all other slots remain integrated under the original law. -/
theorem mixedWeight_energy_le (reference : Slot → FiniteDist Color)
    (fixed : Finset Slot) (weight : Slot → Color → ℝ)
    (hnonneg : ∀ slot color, 0 ≤ weight slot color)
    (hpositive : ∀ slot, 0 < ∑ color, weight slot color)
    (hequal : ∀ slot ∉ fixed, weight slot = (reference slot).weight)
    (kernel : (Slot → Color) → ℝ) :
    (∑ word, (∏ slot, weight slot (word slot)) * kernel word ^ 2) ≤
      (∏ slot, ∑ color, weight slot color) * fiberNorm reference kernel fixed ^ 2 := by
  let alternate (slot : Slot) : FiniteDist Color := {
    weight := fun color => weight slot color / ∑ point, weight slot point
    nonneg := fun color => div_nonneg (hnonneg slot color) (hpositive slot).le
    sum_one := by rw [← Finset.sum_div, div_self (hpositive slot).ne'] }
  have ha : ∀ slot ∉ fixed, alternate slot = reference slot := by
    intro slot hs
    apply FiniteDist.ext
    intro color
    change weight slot color / (∑ point, weight slot point) = _
    rw [hequal slot hs, (reference slot).sum_one, div_one]
  have henergy := l2Sq_le_fiberNorm_of_eq_off_fixed reference alternate fixed ha kernel
  have hmass : 0 ≤ ∏ slot, ∑ color, weight slot color :=
    Finset.prod_nonneg fun slot _ => (hpositive slot).le
  apply le_trans ?_ (mul_le_mul_of_nonneg_left henergy hmass)
  apply le_of_eq
  simp only [FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.independent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro slot _
  change _ = (∑ color, weight slot color) * (weight slot (word slot) / ∑ color, weight slot color)
  exact (mul_div_cancel₀ _ (hpositive slot).ne').symm
end
end AFT.MixedKernel

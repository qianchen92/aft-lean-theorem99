import AFT.PairedJointBoundary
import AFT.TensorMixedSchur

/-! # Full public paired scores have constant Schur bounds -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color Center : Type*} [Fintype Color] [Fintype Center]

/-- The exact matrix of the public paired score, including its compensator. -/
def pairedPublicMatrix (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ) (point : Color) (pair : Color × Center) : ℝ :=
  (if point = pair.1 then 1 else 0) - activation * anchor point pair.2 * primary.weight point / body.weight pair.2

theorem pairedPublicDensity_single (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ) (point : Color) :
    pairedPublicDensity primary body anchor activation (Pi.single point 1) =
      pairedPublicMatrix primary body anchor activation point := by
  funext pair
  simp only [pairedPublicDensity, LinearMap.coe_mk, AddHom.coe_mk, pairedPublicMatrix]
  have he : (∑ color, anchor color pair.2 * (primary.weight color * (Pi.single point (1 : ℝ) : Color → ℝ) color)) =
      anchor point pair.2 * primary.weight point := by
    simp [Pi.single_apply]
  rw [he]
  simp only [Pi.single_apply, eq_comm]
  ring

private theorem pairedPublicMatrix_abs_le (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ) (ha : 0 ≤ activation)
    (hanchor : ∀ color center, 0 ≤ anchor color center) (point : Color) (pair : Color × Center) :
    |pairedPublicMatrix primary body anchor activation point pair| ≤
      (if point = pair.1 then 1 else 0) + activation * anchor point pair.2 * primary.weight point / body.weight pair.2 := by
  apply (abs_sub _ _).trans_eq
  rw [abs_of_nonneg (by split_ifs <;> norm_num : (0 : ℝ) ≤ if point = pair.1 then 1 else 0),
    abs_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg ha (hanchor point pair.2)) (primary.nonneg point)) (body.nonneg pair.2))]

/-- The absolute row sum uses the genuine calibrated anchor comparison,
so fixing any public primary/compensator pair costs a constant. -/
theorem pairedPublicMatrix_row_le (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation comparison : ℝ)
    (ha : 0 ≤ activation) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (pair : Color × Center) :
    1 + (∑ point, |pairedPublicMatrix primary body anchor activation point pair|) ≤ comparison + 2 := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun point _ =>
    pairedPublicMatrix_abs_le primary body anchor activation ha hanchor point pair)
  have he : (∑ point, activation * anchor point pair.2 * primary.weight point / body.weight pair.2) =
      activation * applyAnchor anchor primary.weight pair.2 / body.weight pair.2 := by
    simp only [applyAnchor, Finset.mul_sum, Finset.sum_div, mul_assoc]
  have hratio : activation * applyAnchor anchor primary.weight pair.2 / body.weight pair.2 ≤ comparison := by
    by_cases hb : body.weight pair.2 = 0
    · simpa only [hb, div_zero] using hK
    · exact (div_le_iff₀ (lt_of_le_of_ne (body.nonneg pair.2) (Ne.symm hb))).mpr (hcompare pair.2)
  simp only [Finset.sum_add_distrib, he] at hsum
  have hsingle : (∑ point : Color, if point = pair.1 then (1 : ℝ) else 0) = 1 := by simp
  rw [hsingle] at hsum
  linarith

/-- Integrating the absolute matrix costs at most two. Zero-probability
body atoms are permitted and do not require division cancellation there. -/
theorem pairedPublicMatrix_column_le (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ)
    (ha : 0 ≤ activation) (ha1 : activation ≤ 1)
    (hanchor : ∀ color center, 0 ≤ anchor color center)
    (hmass : ∀ color, ∑ center, anchor color center = 1) (point : Color) :
    (primary.prod body).expectation (fun pair => |pairedPublicMatrix primary body anchor activation point pair|) ≤
      2 * primary.weight point := by
  have hcomp : body.expectation (fun center => activation * anchor point center * primary.weight point / body.weight center) ≤
      activation * primary.weight point := by
    calc
      _ ≤ ∑ center, activation * anchor point center * primary.weight point := by
        apply Finset.sum_le_sum
        intro center _
        by_cases hb : body.weight center = 0
        · simp only [hb, zero_mul]
          exact mul_nonneg (mul_nonneg ha (hanchor point center)) (primary.nonneg point)
        · exact le_of_eq (mul_div_cancel₀ _ hb)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, hmass point, mul_one]
  calc
    _ ≤ (primary.prod body).expectation (fun pair =>
        (if point = pair.1 then 1 else 0) + activation * anchor point pair.2 * primary.weight point / body.weight pair.2) := by
      exact Finset.sum_le_sum fun pair _ => mul_le_mul_of_nonneg_left
        (pairedPublicMatrix_abs_le primary body anchor activation ha hanchor point pair) ((primary.prod body).nonneg pair)
    _ = primary.weight point + body.expectation (fun center =>
        activation * anchor point center * primary.weight point / body.weight center) := by
      rw [FiniteDist.expectation_add, FiniteDist.expectation_prod, FiniteDist.expectation_prod]
      simp only [FiniteDist.expectation_const]
      congr 1
      simp [FiniteDist.expectation, body.sum_one]
    _ ≤ primary.weight point + activation * primary.weight point := add_le_add le_rfl hcomp
    _ ≤ _ := by nlinarith [primary.nonneg point]

/-- The complete joint paired public score has a fixed-order activity
bound with no palette-size or inverse atom-probability factor. -/
theorem pairedPublicDensity_joint_activity_le (count : ℕ)
    (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation comparison : ℝ)
    (ha : 0 ≤ activation) (ha1 : activation ≤ 1) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center)
    (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (rates : Fin count → ℝ) (hrates : ∀ slot, 0 ≤ rates slot)
    (kernel : (Fin count → Color) → ℝ) :
    MixedKernel.activity rates (fun _ => primary.prod body)
      (TensorChannel.applyLinear count (fun _ => pairedPublicDensity primary body anchor activation) kernel) ≤
      (comparison + 2) ^ (2 * count) * MixedKernel.activity rates (fun _ => primary) kernel := by
  have he : TensorChannel.applyLinear count (fun _ => pairedPublicDensity primary body anchor activation) kernel =
      MixedKernel.matrixApply (fun _ => pairedPublicMatrix primary body anchor activation) kernel := by
    funext output
    change TensorChannel.apply count _ kernel output = _
    rw [TensorChannel.apply_formula]
    simp only [pairedPublicDensity_single, MixedKernel.matrixApply]
  rw [he]
  have hh := MixedKernel.matrixApply_activity_le (fun _ : Fin count => primary) (fun _ => primary.prod body)
    (fun _ => pairedPublicMatrix primary body anchor activation) (comparison + 2) (by linarith)
    (fun _ => pairedPublicMatrix_row_le primary body anchor activation comparison ha hK hanchor hcompare)
    (fun _ point => (pairedPublicMatrix_column_le primary body anchor activation ha ha1 hanchor hmass point).trans
      (mul_le_mul_of_nonneg_right (by linarith) (primary.nonneg point))) rates hrates kernel
  simpa only [Fintype.card_fin] using hh
end
end AFT

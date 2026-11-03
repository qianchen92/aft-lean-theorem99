import AFT.PairedPublicSchur
import AFT.TensorMatrixCanonical

/-! # Joint primary/body input kernels on the complete paired public variables -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

/-- The signed public paired matrix has its exact column mean. -/
theorem pairedPublicMatrix_mean (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation : ℝ)
    (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hsupport : ∀ point center, body.weight center = 0 → anchor point center = 0) (point : Color) :
    (primary.prod body).expectation (pairedPublicMatrix primary body anchor activation point) =
      (1 - activation) * primary.weight point := by
  have hcancel (center : Color) : body.weight center *
      (activation * anchor point center * primary.weight point / body.weight center) =
      activation * anchor point center * primary.weight point := by
    by_cases hb : body.weight center = 0
    · simp only [hb, hsupport point center hb, mul_zero, zero_mul, zero_div]
    · exact mul_div_cancel₀ _ hb
  unfold pairedPublicMatrix
  rw [FiniteDist.expectation_sub, FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  simp only [FiniteDist.expectation_const]
  have hfirst : primary.expectation (fun color => if point = color then 1 else 0) = primary.weight point := by
    simp [FiniteDist.expectation]
  have hinner (color : Color) : body.expectation (fun _ => if point = color then (1 : ℝ) else 0) =
      (if point = color then 1 else 0) := FiniteDist.expectation_const body _
  simp_rw [hinner]
  rw [hfirst]
  have hsecond : body.expectation (fun center => activation * anchor point center * primary.weight point / body.weight center) =
      activation * primary.weight point := by
    simp only [FiniteDist.expectation, hcancel, ← Finset.sum_mul, ← Finset.mul_sum, hmass point, mul_one]
  rw [hsecond]
  ring

/-- Ordinary body inputs use their public center. A dummy primary component
lets both pools use one alphabet without changing any observable score. -/
def bodyPublicMatrix (point : Color) (pair : Color × Color) : ℝ :=
  if point = pair.2 then 1 else 0

theorem bodyPublicMatrix_row (pair : Color × Color) : (∑ point, |bodyPublicMatrix point pair|) = 1 := by
  have he (point : Color) : |bodyPublicMatrix point pair| = (if point = pair.2 then 1 else 0) := by
    unfold bodyPublicMatrix
    split_ifs <;> norm_num
  simp_rw [he]
  simp

theorem bodyPublicMatrix_mean (primary body : FiniteDist Color) (point : Color) :
    (primary.prod body).expectation (bodyPublicMatrix point) = body.weight point := by
  rw [FiniteDist.expectation_prod]
  simp only [bodyPublicMatrix]
  simp [FiniteDist.expectation, ← Finset.sum_mul, primary.sum_one]

theorem bodyPublicMatrix_column (primary body : FiniteDist Color) (point : Color) :
    (primary.prod body).expectation (fun pair => |bodyPublicMatrix point pair|) = body.weight point := by
  have he : (fun pair => |bodyPublicMatrix point pair|) = bodyPublicMatrix point := by
    funext pair
    unfold bodyPublicMatrix
    split_ifs <;> norm_num
  rw [he, bodyPublicMatrix_mean]

def publicInputMatrix (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (isPrimary : Bool) : Color → (Color × Color) → ℝ :=
  if isPrimary then pairedPublicMatrix primary body anchor activation else bodyPublicMatrix

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

/-- The literal joint public score, including one distinct compensator for
every primary input and the actual centers for ordinary body inputs. -/
def pairedPublicKernel (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (role : Slot → Bool) (kernel : (Slot → Color) → ℝ) :
    (Slot → (Color × Color)) → ℝ :=
  MixedKernel.matrixApply (fun slot => publicInputMatrix primary body anchor activation (role slot)) kernel

theorem pairedPublicKernel_canonical (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (role : Slot → Bool)
    (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hsupport : ∀ point center, body.weight center = 0 → anchor point center = 0)
    (kernel : (Slot → Color) → ℝ)
    (hc : Hoeffding.Canonical (fun slot => if role slot then primary else body) Finset.univ kernel) :
    Hoeffding.Canonical (fun _ : Slot => primary.prod body) Finset.univ
      (pairedPublicKernel primary body anchor activation role kernel) := by
  apply MixedKernel.matrixApply_canonical _ _ _ (fun slot => if role slot then 1-activation else 1) _ kernel hc
  intro slot point
  by_cases hs : role slot = true
  · simpa [publicInputMatrix, hs] using pairedPublicMatrix_mean primary body anchor activation hmass hsupport point
  · simpa [publicInputMatrix, hs] using bodyPublicMatrix_mean primary body point

theorem pairedPublicKernel_activity_le (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation comparison : ℝ) (ha : 0 ≤ activation) (ha1 : activation ≤ 1) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center)
    (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (role : Slot → Bool) (rates : Slot → ℝ) (hrates : ∀ slot, 0 ≤ rates slot)
    (kernel : (Slot → Color) → ℝ) :
    MixedKernel.activity rates (fun _ : Slot => primary.prod body)
      (pairedPublicKernel primary body anchor activation role kernel) ≤
      (comparison + 2) ^ (2 * Fintype.card Slot) *
        MixedKernel.activity rates (fun slot => if role slot then primary else body) kernel := by
  apply MixedKernel.matrixApply_activity_le _ _ _ (comparison+2) (by linarith) _ _ rates hrates kernel
  · intro slot pair
    by_cases hs : role slot = true
    · simpa [publicInputMatrix, hs] using
        pairedPublicMatrix_row_le primary body anchor activation comparison ha hK hanchor hcompare pair
    · simp only [publicInputMatrix, if_neg hs, bodyPublicMatrix_row]
      linarith
  · intro slot point
    by_cases hs : role slot = true
    · simp only [publicInputMatrix, if_pos hs]
      exact (pairedPublicMatrix_column_le primary body anchor activation ha ha1 hanchor hmass point).trans
        (mul_le_mul_of_nonneg_right (by linarith) (primary.nonneg point))
    · simp only [publicInputMatrix, if_neg hs, bodyPublicMatrix_column]
      exact le_mul_of_one_le_left (body.nonneg point) (by linarith)
theorem pairedPublicKernel_fiberNorm_le (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation comparison : ℝ) (ha : 0 ≤ activation) (ha1 : activation ≤ 1) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center)
    (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (role : Slot → Bool) (fixed : Finset Slot)
    (kernel : (Slot → Color) → ℝ) :
    MixedKernel.fiberNorm (fun _ : Slot => primary.prod body)
      (pairedPublicKernel primary body anchor activation role kernel) fixed ≤
      (comparison + 2) ^ (2 * Fintype.card Slot) *
        MixedKernel.fiberNorm (fun slot => if role slot then primary else body) kernel fixed := by
  apply MixedKernel.matrixApply_fiberNorm_le _ _ _ (comparison+2) (by linarith) _ _ kernel fixed
  · intro slot pair
    by_cases hs : role slot = true
    · simpa [publicInputMatrix, hs] using
        pairedPublicMatrix_row_le primary body anchor activation comparison ha hK hanchor hcompare pair
    · simp only [publicInputMatrix, if_neg hs, bodyPublicMatrix_row]
      linarith
  · intro slot point
    by_cases hs : role slot = true
    · simp only [publicInputMatrix, if_pos hs]
      exact (pairedPublicMatrix_column_le primary body anchor activation ha ha1 hanchor hmass point).trans
        (mul_le_mul_of_nonneg_right (by linarith) (primary.nonneg point))
    · simp only [publicInputMatrix, if_neg hs, bodyPublicMatrix_column]
      exact le_mul_of_one_le_left (body.nonneg point) (by linarith)
end
end AFT

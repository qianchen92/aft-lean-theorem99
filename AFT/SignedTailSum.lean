import AFT.MixtureTail
import AFT.LocalCoefficientLinear

/-! # Complete histogram tails of finite signed linear combinations -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {State Index : Type*} [Fintype State] [Fintype Index]

/-- The exact finite L2 triangle bound with arbitrary signed coefficients.
The bound is a weighted sum of component norms, with no cardinality factor. -/
theorem l2Sq_signed_sum_le (law : FiniteDist State) (coefficient bound : Index → ℝ)
    (value : Index → State → ℝ) (hbound : ∀ index, 0 ≤ bound index)
    (hvalue : ∀ index, law.l2Sq (value index) ≤ bound index ^ 2) :
    law.l2Sq (fun point => ∑ index, coefficient index * value index point) ≤
      (∑ index, |coefficient index| * bound index) ^ 2 := by
  have hcross (first second : Index) :
      |law.expectation (fun point => value first point * value second point)| ≤ bound first * bound second := by
    have hc := CanonicalMoments.expectation_mul_sq_le law (value first) (value second)
    have hb := mul_le_mul (hvalue first) (hvalue second) (law.l2Sq_nonneg _) (sq_nonneg _)
    have hs : |law.expectation (fun point => value first point * value second point)| ^ 2 ≤
        (bound first * bound second) ^ 2 := by simpa only [sq_abs, mul_pow] using hc.trans hb
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (hbound first) (hbound second))).mp hs
  have hexpand : law.l2Sq (fun point => ∑ index, coefficient index * value index point) =
      ∑ first, ∑ second, coefficient first * coefficient second *
        law.expectation (fun point => value first point * value second point) := by
    unfold l2Sq expectation
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro second _
    apply Finset.sum_congr rfl
    intro point _
    ring
  rw [hexpand]
  calc
    _ ≤ ∑ first, ∑ second,
        (|coefficient first| * bound first) * (|coefficient second| * bound second) := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      calc
        _ ≤ |coefficient first * coefficient second * law.expectation (fun point => value first point * value second point)| := le_abs_self _
        _ ≤ |coefficient first| * |coefficient second| * (bound first * bound second) := by
          simp only [abs_mul]
          exact mul_le_mul_of_nonneg_left (hcross first second) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul_sum]; ring

end
end AFT.FiniteDist

namespace AFT.HistogramNormalization
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
noncomputable section
variable {Slot Color Index : Type*} [Fintype Slot] [Fintype Color] [Fintype Index]

/-- Complete truncation of the actual signed mass is a literal linear map. -/
def densityTailLinear (reference : FiniteDist Color) (cutoff : ℕ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] ((Slot → Color) → ℝ) where
  toFun mass := densityTail reference mass cutoff
  map_add' first second := by
    funext word
    simp only [densityTail, Hoeffding.densityComponent, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar mass := by
    funext word
    simp only [densityTail, Hoeffding.densityComponent, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected _
    apply Finset.sum_congr rfl
    intro input _
    ring

/-- Symmetrization followed by the complete degree tail is a linear map on
actual physical signed laws. -/
def symmetrizedTailLinear (reference : FiniteDist Color) (cutoff : ℕ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] ((Slot → Color) → ℝ) :=
  (densityTailLinear reference cutoff).comp LocalTensors.symmetrizeLinear

/-- The componentwise complete tail estimates extend to every finite signed
control representation, paying its actual weighted sum of input bounds. -/
theorem signed_sum_complete_tail_le (reference : FiniteDist Color) (cutoff : ℕ)
    (coefficient bound : Index → ℝ) (mass : Index → (Slot → Color) → ℝ)
    (hbound : ∀ index, 0 ≤ bound index)
    (hcomponent : ∀ index,
      (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
        (densityTail reference (symmetrizedMass (mass index)) cutoff) ≤ bound index ^ 2) :
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
      (densityTail reference (symmetrizedMass (fun word => ∑ index, coefficient index * mass index word)) cutoff) ≤
        (∑ index, |coefficient index| * bound index) ^ 2 := by
  have hid : (fun word => ∑ index, coefficient index * mass index word) =
      ∑ index, coefficient index • mass index := by ext word; simp
  have htail : densityTail reference
      (symmetrizedMass (fun word => ∑ index, coefficient index * mass index word)) cutoff =
      fun word => ∑ index, coefficient index * densityTail reference (symmetrizedMass (mass index)) cutoff word := by
    change (symmetrizedTailLinear (Slot := Slot) reference cutoff)
      (fun word => ∑ index, coefficient index * mass index word) = _
    rw [hid, map_sum]
    funext word
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [htail]
  exact FiniteDist.l2Sq_signed_sum_le _ coefficient bound _ hbound hcomponent

end
end AFT.HistogramNormalization

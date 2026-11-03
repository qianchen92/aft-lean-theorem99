import AFT.MixedSingleton
import AFT.MixedTensor
import AFT.MixedEquiv
import AFT.MixedSymmetry

/-! # Products and subtractions with every mixed density fiber retained -/

namespace AFT.MixedKernel

open scoped BigOperators Classical
noncomputable section

variable {Color : Type*} [Fintype Color]

theorem activity_sub_le {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (first second : (Slot → Color) → ℝ) (hrate : ∀ slot, 0 ≤ rate slot) :
    activity rate reference (first - second) ≤ activity rate reference first + activity rate reference second := by
  have h := activity_add_le rate reference first ((-1 : ℝ) • second) hrate
  rw [activity_smul] at h
  simpa only [abs_neg, abs_one, one_mul, neg_one_smul, ← sub_eq_add_neg] using h

theorem pair_product_activity_le (first second : FiniteDist Color) (f g : Color → ℝ)
    (a b F X G Y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : 0 ≤ F) (hX : 0 ≤ X) (hG : 0 ≤ G) (hY : 0 ≤ Y)
    (hf : (∑ color, first.weight color * f color ^ 2) ≤ F ^ 2)
    (hfx : ∀ color, |f color| ≤ X)
    (hg : (∑ color, second.weight color * g color ^ 2) ≤ G ^ 2)
    (hgy : ∀ color, |g color| ≤ Y) :
    activity ![a,b] (pairReference first second) (pairKernel (fun x y => f x * g y)) ≤
      a * b * (F + a * X) * (G + b * Y) := by
  have hfx2 (color) : f color ^ 2 ≤ X ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hfx color) 2
  have hgy2 (color) : g color ^ 2 ≤ Y ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hgy color) 2
  have hfull : (∑ x, ∑ y, first.weight x * second.weight y * (f x * g y)^2) ≤ (F*G)^2 := by
    calc
      _ = (∑ x, first.weight x * f x^2) * (∑ y, second.weight y * g y^2) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ F^2*G^2 := mul_le_mul hf hg (Finset.sum_nonneg fun y _ => mul_nonneg (second.nonneg y) (sq_nonneg _)) (sq_nonneg _)
      _ = _ := by ring
  have hleft (x) : (∑ y, second.weight y * (f x*g y)^2) ≤ (X*G)^2 := by
    calc
      _ = f x^2 * ∑ y, second.weight y * g y^2 := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
      _ ≤ X^2*G^2 := mul_le_mul (hfx2 x) hg (Finset.sum_nonneg fun y _ => mul_nonneg (second.nonneg y) (sq_nonneg _)) (sq_nonneg _)
      _ = _ := by ring
  have hright (y) : (∑ x, first.weight x * (f x*g y)^2) ≤ (F*Y)^2 := by
    calc
      _ = (∑ x, first.weight x * f x^2) * g y^2 := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro x _; ring
      _ ≤ F^2*Y^2 := mul_le_mul hf (hgy2 y) (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hh := pair_activity_le first second (fun x y => f x*g y) a b (F*G) (X*G) (F*Y) (X*Y)
    ha hb (mul_nonneg hF hG) (mul_nonneg hX hG) (mul_nonneg hF hY) (mul_nonneg hX hY)
    hfull hleft hright (fun x y => by rw [abs_mul]; exact mul_le_mul (hfx x) (hgy y) (abs_nonneg _) hX)
  exact hh.trans_eq (by ring)

end
end AFT.MixedKernel

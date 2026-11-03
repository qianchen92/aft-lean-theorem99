import AFT.MixedCanonical
import AFT.MixedTensor

/-! # Disjoint products retain exact canonicality -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
local instance canonicalTensorSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Left Right Color : Type*} [Fintype Left] [Fintype Right] [Fintype Color]

theorem tensor_canonical (left : Left → FiniteDist Color) (right : Right → FiniteDist Color)
    (first : (Left → Color) → ℝ) (second : (Right → Color) → ℝ)
    (hf : Hoeffding.Canonical left Finset.univ first)
    (hs : Hoeffding.Canonical right Finset.univ second) :
    Hoeffding.Canonical (Sum.elim left right) Finset.univ (tensor first second) := by
  constructor
  · intro x y hxy
    exact congrArg (tensor first second) (funext fun slot => hxy slot (Finset.mem_univ _))
  · intro slot _ word
    cases slot with
    | inl slot =>
      have hleft (color : Color) : Function.update word (Sum.inl slot) color ∘ Sum.inl =
          Function.update (word ∘ Sum.inl) slot color := by
        funext other
        by_cases h : other = slot <;> simp [Function.update, h]
      have hright (color : Color) : Function.update word (Sum.inl slot) color ∘ Sum.inr = word ∘ Sum.inr := by
        funext other
        simp
      calc
        _ = ∑ color, (left slot).weight color *
            (first (Function.update (word ∘ Sum.inl) slot color) * second (word ∘ Sum.inr)) := by
          apply Finset.sum_congr rfl
          intro color _
          exact congrArg ((left slot).weight color * ·)
            (congrArg₂ (· * ·) (congrArg first (hleft color)) (congrArg second (hright color)))
        _ = 0 := by
          rw [show (∑ color, (left slot).weight color *
              (first (Function.update (word ∘ Sum.inl) slot color) * second (word ∘ Sum.inr))) =
            (∑ color, (left slot).weight color * first (Function.update (word ∘ Sum.inl) slot color)) *
              second (word ∘ Sum.inr) by simp only [Finset.sum_mul, mul_assoc]]
          rw [hf.2 slot (Finset.mem_univ _) (word ∘ Sum.inl), zero_mul]
    | inr slot =>
      have hright (color : Color) : Function.update word (Sum.inr slot) color ∘ Sum.inr =
          Function.update (word ∘ Sum.inr) slot color := by
        funext other
        by_cases h : other = slot <;> simp [Function.update, h]
      have hleft (color : Color) : Function.update word (Sum.inr slot) color ∘ Sum.inl = word ∘ Sum.inl := by
        funext other
        simp
      calc
        _ = ∑ color, (right slot).weight color *
            (first (word ∘ Sum.inl) * second (Function.update (word ∘ Sum.inr) slot color)) := by
          apply Finset.sum_congr rfl
          intro color _
          exact congrArg ((right slot).weight color * ·)
            (congrArg₂ (· * ·) (congrArg first (hleft color)) (congrArg second (hright color)))
        _ = first (word ∘ Sum.inl) * ∑ color, (right slot).weight color *
            second (Function.update (word ∘ Sum.inr) slot color) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro color _
          ring
        _ = 0 := by rw [hs.2 slot (Finset.mem_univ _) (word ∘ Sum.inr), mul_zero]

end
end AFT.MixedKernel

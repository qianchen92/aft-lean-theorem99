import AFT.V7Blocks
import AFT.BlockCoefficientNorms

/-! # Physical V7 block budgets, including every nonlinear degree -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts
open scoped BigOperators Classical Topology

noncomputable section

local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

/-- The exact numbers of the two physical block types are retained when
summing their normalized linear, quadratic, and cubic norms. -/
theorem actual_normalized_block_budgets_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root queue : blockIndex parameter → ℤ,
      (∀ index, |root index| ≤ (v7RootCutoff parameter : ℤ)) →
      (∀ index, |queue index| ≤ (queueCutoff parameter : ℤ)) → ∀ scale : ℝ, 0 ≤ scale →
      let law := actualBlockFamily cutoffScale parameter (beta parameter) root queue
      let reference := actualReferenceLaw cutoffScale parameter (beta parameter)
      (∑ index, ∑ color, normalizedLinear (blockSlots parameter) reference law scale index color ^ 2) ≤
        scale ^ 2 * ((Parameters.legs parameter : ℝ) * (100000 * (parameter : ℝ) ^ 22) +
          (Parameters.bodies parameter - Parameters.legs parameter : ℕ) * (10944 / (parameter : ℝ) ^ 38)) ∧
      (∑ index, (128 * SelectionBound.localPairNorm (normalizedQuadratic (blockSlots parameter) reference law scale) index +
          128 * Real.sqrt (Parameters.bodies parameter) *
            SelectionBound.localTripleNorm (normalizedCubic (blockSlots parameter) reference law scale) index)) ≤
        128 * Parameters.legs parameter *
          (scale ^ 2 * (1256 * (parameter : ℝ) ^ 15) +
            Real.sqrt (Parameters.bodies parameter) * scale ^ 3 * (1256 * (parameter : ℝ) ^ 15)) := by
  filter_upwards [actual_block_coefficient_bounds_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hcoef hlarge root queue hr hq scale hs
  have hc := hcoef root queue hr hq
  dsimp only at hc ⊢
  let law := actualBlockFamily cutoffScale parameter (beta parameter) root queue
  let reference := actualReferenceLaw cutoffScale parameter (beta parameter)
  let coefficient := localCoefficient (blockSlots parameter) reference law
  let B := 1256 * (parameter : ℝ) ^ 15
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hleg (leg) (degree) : BlockFock.tensorEnergy (coefficient (.inl leg) degree) ≤ B ^ 2 := by
    have hp : 1576960 * (parameter : ℝ) ^ 30 ≤ B ^ 2 := by
      have heq : B ^ 2 = 1577536 * (parameter : ℝ) ^ 30 := by dsimp only [B]; ring
      rw [heq]
      nlinarith [pow_nonneg (Nat.cast_nonneg parameter : (0 : ℝ) ≤ parameter) 30]
    exact (hc.2.1 leg degree).trans hp
  have hbodyQ (body) : normalizedQuadratic (blockSlots parameter) reference law scale (.inr body) = 0 := by
    funext word
    change scale ^ 2 * coefficient (.inr body) 2 word = 0
    have hz : coefficient (.inr body) 2 = 0 := hc.2.2.2 body 2 (by norm_num)
    rw [hz]
    simp only [Pi.zero_apply, mul_zero]
  have hbodyC (body) : normalizedCubic (blockSlots parameter) reference law scale (.inr body) = 0 := by
    funext word
    change scale ^ 3 * coefficient (.inr body) 3 word = 0
    have hz : coefficient (.inr body) 3 = 0 := hc.2.2.2 body 3 (by norm_num)
    rw [hz]
    simp only [Pi.zero_apply, mul_zero]
  refine ⟨?_, ?_⟩
  · simp_rw [normalized_linear_energy]
    rw [Fintype.sum_sum_type]
    calc
      _ ≤ (∑ _leg : Fin (Parameters.legs parameter), scale ^ 2 * (100000 * (parameter : ℝ) ^ 22)) +
          ∑ _body : Fin (Parameters.bodies parameter - Parameters.legs parameter), scale ^ 2 * (10944 / (parameter : ℝ) ^ 38) := by
        apply add_le_add
        · exact Finset.sum_le_sum fun leg _ => mul_le_mul_of_nonneg_left (hc.1 leg) (sq_nonneg scale)
        · exact Finset.sum_le_sum fun body _ => mul_le_mul_of_nonneg_left (hc.2.2.1 body) (sq_nonneg scale)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · rw [Fintype.sum_sum_type]
    change (∑ leg : Fin (Parameters.legs parameter),
      (128 * SelectionBound.localPairNorm (normalizedQuadratic (blockSlots parameter) reference law scale) (.inl leg) +
        128 * Real.sqrt (Parameters.bodies parameter) * SelectionBound.localTripleNorm
          (normalizedCubic (blockSlots parameter) reference law scale) (.inl leg))) +
      (∑ body : Fin (Parameters.bodies parameter - Parameters.legs parameter),
      (128 * SelectionBound.localPairNorm (normalizedQuadratic (blockSlots parameter) reference law scale) (.inr body) +
        128 * Real.sqrt (Parameters.bodies parameter) * SelectionBound.localTripleNorm
          (normalizedCubic (blockSlots parameter) reference law scale) (.inr body))) ≤ _
    have hz (body) : 128 * SelectionBound.localPairNorm (normalizedQuadratic (blockSlots parameter) reference law scale) (.inr body) +
        128 * Real.sqrt (Parameters.bodies parameter) * SelectionBound.localTripleNorm
          (normalizedCubic (blockSlots parameter) reference law scale) (.inr body) = 0 := by
      simp only [SelectionBound.localPairNorm, SelectionBound.localTripleNorm, hbodyQ, hbodyC,
        BlockFock.tensorEnergy, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, Real.sqrt_zero, mul_zero, add_zero]
    simp only [hz, Finset.sum_const_zero, add_zero]
    calc
      _ ≤ ∑ _leg : Fin (Parameters.legs parameter),
          (128 * (scale ^ 2 * B) + 128 * Real.sqrt (Parameters.bodies parameter) * (scale ^ 3 * B)) := by
        apply Finset.sum_le_sum
        intro leg _
        exact add_le_add
          (mul_le_mul_of_nonneg_left (normalized_quadratic_norm_le (blockSlots parameter) reference law scale B (.inl leg) hB (hleg leg 2)) (by norm_num))
          (mul_le_mul_of_nonneg_left (normalized_cubic_norm_le (blockSlots parameter) reference law scale B (.inl leg) hs hB (hleg leg 3)) (by positivity))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, B]; ring

end

end AFT.V7Calibration

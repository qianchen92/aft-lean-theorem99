import AFT.BlockCoefficientNorms

/-! # Full untagged tails from the doubled-radius physical block conditions -/

namespace AFT.BlockProducts

open scoped BigOperators Classical

noncomputable section

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

local instance doubledBlockTailSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _

theorem CubicBlockConditions_scaled (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (population capacity : ℕ) (radius : ℝ)
    (hlocal : CubicBlockConditions Slots reference law population capacity radius) :
    (SelectionBound.nonlinearSupport
      (normalizedQuadratic Slots reference law (Real.sqrt 2 * radius / Real.sqrt population))
      (normalizedCubic Slots reference law (Real.sqrt 2 * radius / Real.sqrt population))).card ≤ capacity ∧
    (∑ index, ∑ color, normalizedLinear Slots reference law
      (Real.sqrt 2 * radius / Real.sqrt population) index color ^ 2) ≤ 1 / 8 ∧
    (∑ index, (128 * SelectionBound.localPairNorm
      (normalizedQuadratic Slots reference law (Real.sqrt 2 * radius / Real.sqrt population)) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (normalizedCubic Slots reference law (Real.sqrt 2 * radius / Real.sqrt population)) index)) ≤ 1 / 2 := by
  have hq : (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
      (radius / Real.sqrt population) index word) =
      normalizedQuadratic Slots reference law (Real.sqrt 2 * radius / Real.sqrt population) := by
    funext index word
    simp only [normalizedQuadratic, mul_pow, div_pow]
    ring
  have hc : (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
      (radius / Real.sqrt population) index word) =
      normalizedCubic Slots reference law (Real.sqrt 2 * radius / Real.sqrt population) := by
    funext index word
    simp only [normalizedCubic, mul_pow, div_pow]
    ring
  change _ ∧ _ ∧ _ at hlocal
  rw [hq, hc] at hlocal
  refine ⟨hlocal.1, ?_, hlocal.2.2⟩
  simpa only [normalizedLinear, mul_div_assoc, mul_assoc] using hlocal.2.1

set_option backward.isDefEq.respectTransparency false in
/-- The actual whole-population density tail follows from the doubled
local conditions, with its complete all-orders normalization. -/
theorem untagged_complete_tail_of_doubled [Nonempty Color]
    (reference : FiniteDist Color) (href : ∀ color, 0 < reference.weight color)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (hslots : ∀ index, Fintype.card (Slots index) ≤ 3) (cutoff capacity : ℕ) (radius : ℝ)
    (hpopulation : 0 < Fintype.card (Sigma Slots)) (hradius : Real.exp 1 ≤ radius ^ 2)
    (hlocal : CubicBlockConditions Slots reference law (Fintype.card (Sigma Slots)) capacity radius) :
    (FiniteDist.independent (fun _ : Sigma Slots => reference)).l2Sq
      (HistogramNormalization.densityTail reference
        (HistogramNormalization.symmetrizedMass (blockMass Slots law)) cutoff) ≤
      (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) *
        (16 * Real.exp (8 * ∑ color, (∑ index, Real.sqrt 2 * normalizedLinear Slots reference law
          (radius / Real.sqrt (Fintype.card (Sigma Slots))) index color) ^ 2)) := by
  have hc := CubicBlockConditions_scaled Slots reference law (Fintype.card (Sigma Slots)) capacity radius hlocal
  have hrad : (Real.sqrt 2 * radius) ^ 2 = 2 * radius ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpositive : 0 < radius ^ 2 := (Real.exp_pos 1).trans_le hradius
  have hh := actual_block_complete_tail Slots reference law hslots cutoff capacity (Real.sqrt 2 * radius)
    hpopulation (by rw [hrad]; linarith) hc.1 hc.2.1 hc.2.2
  rw [HistogramNormalization.symmetrized_densityTail_energy reference href (blockMass Slots law) cutoff]
  apply hh.trans
  have hfactor : (Real.exp 1 / (Real.sqrt 2 * radius) ^ 2) ^ (cutoff + 1) ≤
      (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) := by
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_left (Real.exp_nonneg _) hpositive
    rw [hrad]
    linarith
  have hmean : (fun color => ∑ index, normalizedLinear Slots reference law
      (Real.sqrt 2 * radius / Real.sqrt (Fintype.card (Sigma Slots))) index color) =
      (fun color => ∑ index, Real.sqrt 2 * normalizedLinear Slots reference law
        (radius / Real.sqrt (Fintype.card (Sigma Slots))) index color) := by
    funext color
    simp only [normalizedLinear, mul_div_assoc, mul_assoc]
  simp_rw [congrFun hmean] at hh ⊢
  exact mul_le_mul_of_nonneg_right hfactor (by positivity)

end

end AFT.BlockProducts

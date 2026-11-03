import AFT.ActualNormalizedMean
import AFT.DoubledBlockTail
import AFT.V7CubicSmallness

/-! # Complete histogram tails of the literal V7 blocks at fixed sources -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology

noncomputable section

local instance actualBlockTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualBlockTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualBlockTailSigmaDecEq (parameter : ℕ) : DecidableEq (Sigma (blockSlots parameter)) := Classical.decEq _

set_option backward.isDefEq.respectTransparency false in
/-- The full all-orders physical histogram tail, with all block smallness
conditions discharged by the V7 parameter formulas. -/
theorem actual_pointwise_complete_tail_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ word : actualRootWord parameter, ∀ queue : blockIndex parameter → ℤ,
      (∀ index, |queue index| ≤ (queueCutoff parameter : ℤ)) → ∀ cutoff : ℕ,
      (FiniteDist.independent (fun _ : Sigma (blockSlots parameter) =>
        actualReferenceLaw cutoffScale parameter (beta parameter))).l2Sq
          (densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
            (symmetrizedMass (blockMass (blockSlots parameter)
              (actualBlockFamily cutoffScale parameter (beta parameter) (actualRootField parameter word) queue))) cutoff) ≤
        (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) *
          (16 * Real.exp (8 * ‖actualNormalizedBlockMean cutoffScale parameter (beta parameter) word queue‖ ^ 2)) := by
  filter_upwards [actual_cubic_conditions_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hc hr hl hp word queue hqueue cutoff
  letI : NeZero (Parameters.modulus parameter) := ⟨(Parameters.modulus_prime parameter).ne_zero⟩
  have href (color) : 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.2.2]
    have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
    have hlo : 0 < 1 / (2 * (Parameters.modulus parameter : ℝ)) := by positivity
    exact hlo.trans_le (hr color)
  have hpopulation : 0 < Fintype.card (Sigma (blockSlots parameter)) := by
    rw [blockSlots_card]
    have hb := Parameters.bodies_positive parameter
    have hn := Parameters.population_identity parameter
    omega
  have hx : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hrad : Real.exp 1 ≤ ((parameter : ℝ) ^ 2) ^ 2 := by
    have hs : (4 : ℝ) ≤ (parameter : ℝ) ^ 2 := by nlinarith
    nlinarith [Real.exp_one_lt_three]
  have hlocal : CubicBlockConditions (blockSlots parameter)
      (actualReferenceLaw cutoffScale parameter (beta parameter))
      (actualBlockFamily cutoffScale parameter (beta parameter) (actualRootField parameter word) queue)
      (Fintype.card (Sigma (blockSlots parameter))) (Parameters.bodies parameter) ((parameter : ℝ) ^ 2) := by
    rw [blockSlots_card]
    exact hc _ _ (actualRootField_bound parameter word) hqueue
  have hh := untagged_complete_tail_of_doubled (blockSlots parameter)
    (actualReferenceLaw cutoffScale parameter (beta parameter)) href
    (actualBlockFamily cutoffScale parameter (beta parameter) (actualRootField parameter word) queue)
    (blockSlots_le_three parameter) cutoff (Parameters.bodies parameter) ((parameter : ℝ) ^ 2)
    hpopulation hrad hlocal
  have hmean := actual_normalized_mean_square cutoffScale parameter (beta parameter) href
    (actualRootField parameter word) queue (actualFockScale parameter)
  have heq (index color) : Real.sqrt 2 * normalizedLinear (blockSlots parameter)
      (actualReferenceLaw cutoffScale parameter (beta parameter))
      (actualBlockFamily cutoffScale parameter (beta parameter) (actualRootField parameter word) queue)
      ((parameter : ℝ) ^ 2 / Real.sqrt (Fintype.card (Sigma (blockSlots parameter)))) index color =
      normalizedLinear (blockSlots parameter) (actualReferenceLaw cutoffScale parameter (beta parameter))
        (actualBlockFamily cutoffScale parameter (beta parameter) (actualRootField parameter word) queue)
        (actualFockScale parameter) index color := by
    simp only [normalizedLinear, actualFockScale, blockSlots_card, mul_assoc]
  simp only [heq, hmean, ← pow_mul, show 2 * 2 = 4 by decide] at hh
  exact hh

end

end AFT.V7Calibration

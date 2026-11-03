import AFT.RestrictedMeanConcentration

/-! # Complete physical marked-block tails with arbitrary joint signed output -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
local instance actualTaggedTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualTaggedTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualTaggedTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

abbrev actualMarkedSlots (parameter : ℕ) (selected : Finset (blockIndex parameter)) :=
  Sigma (fun index : {i : blockIndex parameter // i ∈ selected} => blockSlots parameter index)

abbrev actualRemainingSlots (parameter : ℕ) (selected : Finset (blockIndex parameter)) :=
  Sigma (fun index : {i : blockIndex parameter // i ∉ selected} => blockSlots parameter index)

/-- A joint signed law on every marked output, tensored with the literal
independent physical complement. The tagged tensor need not factor. -/
def actualMarkedBlockMass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (selected : Finset (blockIndex parameter))
    (tagged : (actualMarkedSlots parameter selected → Fin (Parameters.modulus parameter)) → ℝ)
    (word : actualRootWord parameter) (queue : blockIndex parameter → ℤ) :
    ((actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected) → Fin (Parameters.modulus parameter)) → ℝ :=
  taggedBlockMass (fun index : {i : blockIndex parameter // i ∉ selected} => blockSlots parameter index)
    tagged (fun index => actualBlockFamily cutoffScale parameter beta (actualRootField parameter word) queue index)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual complement has its exact coefficient mean, with only the
marked blocks removed. The original whole-output denominator is retained. -/
theorem actual_remaining_coefficient_square (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (href : ∀ color, 0 < (actualReferenceLaw cutoffScale parameter beta).weight color)
    (word : actualRootWord parameter) (queue : blockIndex parameter → ℤ) (selected : Finset (blockIndex parameter)) :
    (∑ color, (∑ index : {i : blockIndex parameter // i ∉ selected},
      Real.sqrt 2 * normalizedLinear (fun index : {i : blockIndex parameter // i ∉ selected} => blockSlots parameter index)
        (actualReferenceLaw cutoffScale parameter beta)
        (fun index => actualBlockFamily cutoffScale parameter beta (actualRootField parameter word) queue index)
        ((parameter : ℝ) ^ 2 / Real.sqrt (Parameters.dimension parameter)) index color) ^ 2) =
      ‖actualRemainingMean cutoffScale parameter beta word queue selected‖ ^ 2 := by
  have hv := remaining_linear_mean (blockSlots parameter) (actualReferenceLaw cutoffScale parameter beta)
    (actualBlockFamily cutoffScale parameter beta (actualRootField parameter word) queue) (actualFockScale parameter) selected
  rw [actual_linear_mean_eq cutoffScale parameter beta href word queue] at hv
  change _ = actualRemainingMean cutoffScale parameter beta word queue selected at hv
  rw [← hv, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro color _
  simp only [WithLp.ofLp_sum, Finset.sum_apply, linearVector_apply, Real.norm_eq_abs, sq_abs,
    normalizedLinear, actualFockScale, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The complete fixed-source signed histogram tail has no independent-block
smallness hypotheses: those are all discharged for the actual V7 blocks. -/
theorem actual_marked_pointwise_tail_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ selected : Finset (blockIndex parameter),
      ∀ tagged : (actualMarkedSlots parameter selected → Fin (Parameters.modulus parameter)) → ℝ,
      ∀ word : actualRootWord parameter, ∀ queue : blockIndex parameter → ℤ,
      (∀ index, |queue index| ≤ (queueCutoff parameter : ℤ)) → ∀ cutoff : ℕ,
      (FiniteDist.independent (fun _ : actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected =>
        actualReferenceLaw cutoffScale parameter (beta parameter))).l2Sq
        (densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (actualMarkedBlockMass cutoffScale parameter (beta parameter) selected tagged word queue)) cutoff) ≤
        (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) *
          (taggedCoefficientEnergy (actualReferenceLaw cutoffScale parameter (beta parameter)) tagged
            (Parameters.dimension parameter) ((parameter : ℝ) ^ 2) *
            (16 * Real.exp (8 * ‖actualRemainingMean cutoffScale parameter (beta parameter) word queue selected‖ ^ 2))) := by
  filter_upwards [actual_restricted_cubic_conditions_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hc hr hl hp selected tagged word queue hqueue cutoff
  letI : NeZero (Parameters.modulus parameter) := ⟨(Parameters.modulus_prime parameter).ne_zero⟩
  have href (color) : 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.2.2]
    have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
    exact (by positivity : 0 < 1 / (2 * (Parameters.modulus parameter : ℝ))).trans_le (hr color)
  have hcard : Fintype.card (actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected) =
      Parameters.dimension parameter := (splitSlots_card (blockSlots parameter) selected).trans (blockSlots_card parameter)
  have hpopulation : 0 < Fintype.card (actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected) := by
    rw [hcard]
    have hb := Parameters.bodies_positive parameter
    have hn := Parameters.population_identity parameter
    omega
  have hx : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hrad : Real.exp 1 ≤ ((parameter : ℝ) ^ 2) ^ 2 := by
    have hs : (4 : ℝ) ≤ (parameter : ℝ) ^ 2 := by nlinarith
    nlinarith [Real.exp_one_lt_three]
  have hlocal := hc (actualRootField parameter word) queue (actualRootField_bound parameter word) hqueue selected
  rw [← hcard] at hlocal
  have hh := tagged_block_complete_tail
    (fun index : {i : blockIndex parameter // i ∉ selected} => blockSlots parameter index)
    (actualReferenceLaw cutoffScale parameter (beta parameter)) href tagged
    (fun index => actualBlockFamily cutoffScale parameter (beta parameter) (actualRootField parameter word) queue index)
    (fun index => blockSlots_le_three parameter index) cutoff (Parameters.bodies parameter) ((parameter : ℝ) ^ 2)
    hpopulation hrad hlocal
  rw [hcard, actual_remaining_coefficient_square cutoffScale parameter (beta parameter) href word queue selected] at hh
  simpa only [← pow_mul, show 2 * 2 = 4 by decide] using hh

end
end AFT.V7Calibration

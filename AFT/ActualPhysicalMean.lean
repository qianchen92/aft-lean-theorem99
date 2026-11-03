import AFT.ActualRootLaw
import AFT.ActualMeanCalibration
import AFT.FiniteExpectationAlgebra

/-! # The actual shared-queue, conditioned-root mixture has the calibrated mean -/

namespace AFT.V7Calibration

open Filter GaussianSource FiniteDist FiniteConcentration ProfileHilbert
open scoped BigOperators Classical Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

local instance actualPhysicalMeanFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualPhysicalMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def actualQueueMarginal (parameter : ℕ) : FiniteDist (Option (Window (queueCutoff parameter))) :=
  optional (windowGaussian parameter (queueCutoff parameter)) (queueRate parameter)
    (by unfold queueRate; positivity) ((body_rates_le_quarter parameter).2.trans (by norm_num))

theorem actual_root_queue_expectation (parameter : ℕ) (index : blockIndex parameter) (f : ℤ → ℤ → ℝ) :
    (FiniteDist.retype (actualQueuePlacementLaw parameter)).expectation (fun sample =>
      (actualRootConditionLaw parameter).expectation (fun word =>
        f (actualRootField parameter word index) (actualQueueShifts parameter sample index))) =
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter)).expectation (fun root =>
        (actualQueueMarginal parameter).expectation (fun queue => f root (optionalShift queue))) := by
  have hr (q : ℤ) :
      (actualRootConditionLaw parameter).expectation (fun word => f (actualRootField parameter word index) q) =
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)).expectation (fun root => f root q) := by
    rw [← actualRootConditionLaw_coordinate parameter (actualRootIndex parameter index), expectation_map]
    rfl
  simp_rw [hr]
  rw [expectation_comm]
  apply congrArg
  funext root
  rw [expectation_retype]
  exact actualQueueShifts_expectation parameter index (f root)

/-- Counting attached and free bodies gives the optional-source blur exactly;
the common queue has only been marginalized at one index at a time. -/
theorem actual_body_population_expectation (cutoffScale : ℝ) (parameter : ℕ) (f : ℤ → ℝ) :
    (∑ index : blockIndex parameter,
      (FiniteDist.retype (actualQueuePlacementLaw parameter)).expectation (fun sample =>
        (actualRootConditionLaw parameter).expectation (fun word =>
          match index with
          | .inl _ => (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).expectation
              (fun source => f (actualRootField parameter word index + source + actualQueueShifts parameter sample index))
          | .inr _ => f (actualRootField parameter word index + actualQueueShifts parameter sample index)))) =
    (Parameters.bodies parameter : ℝ) *
      (bodyBlur cutoffScale parameter).expectation (fun sample => f (bodyShift cutoffScale parameter sample)) := by
  have hcount : Parameters.legs parameter ≤ Parameters.bodies parameter := by
    have hh := (body_rates_le_quarter parameter).1.trans (by norm_num : (1 : ℝ) / 4 ≤ 1)
    have hb : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
    exact_mod_cast (div_le_one hb).mp hh
  have hb : (Parameters.bodies parameter : ℝ) ≠ 0 := by
    exact_mod_cast (Parameters.bodies_positive parameter).ne'
  rw [Fintype.sum_sum_type]
  dsimp only []
  have ha (leg : Fin (Parameters.legs parameter)) := actual_root_queue_expectation parameter (.inl leg)
    (fun root queue => (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).expectation
      (fun source => f (root + source + queue)))
  have hf (body : Fin (Parameters.bodies parameter - Parameters.legs parameter)) :=
    actual_root_queue_expectation parameter (.inr body) (fun root queue => f (root + queue))
  simp_rw [ha, hf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [bodyBlur, bodySample, bodyShift, extraBlur, extraSample, extraShift, expectation_prod]
  simp only [expectation_optional (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)),
    optionalShift, zero_add]
  change _ = (Parameters.bodies parameter : ℝ) *
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter)).expectation (fun root =>
      (1 - legRate parameter) * (actualQueueMarginal parameter).expectation
        (fun queue => f ((root : ℤ) + optionalShift queue)) +
      legRate parameter * (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).expectation
        (fun source => (actualQueueMarginal parameter).expectation
          (fun queue => f ((root : ℤ) + ((source : ℤ) + optionalShift queue)))))
  simp_rw [← add_assoc, expectation_comm (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))
    (actualQueueMarginal parameter)]
  rw [expectation_add, expectation_const_mul, expectation_const_mul]
  rw [Nat.cast_sub hcount]
  unfold legRate
  simp only [optionalShift]
  field_simp
  ring

/-- Summing the actual body's marginals over all physical positions agrees
with the calibrated blur, without asserting independence of those positions. -/
theorem actual_body_mean_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color : Fin (Parameters.modulus parameter),
      (∑ index : blockIndex parameter,
        (FiniteDist.retype (actualQueuePlacementLaw parameter)).expectation (fun sample =>
          (actualRootConditionLaw parameter).expectation (fun word =>
            (actualBlockBodyLaw cutoffScale parameter (beta parameter) index
              (actualRootField parameter word index) (actualQueueShifts parameter sample index)).weight color))) =
        (Parameters.bodies parameter : ℝ) * actualFullBodyProfile cutoffScale parameter (beta parameter) color := by
  filter_upwards [actual_shifted_body_law_eventually cutoffScale hscale beta hbeta]
    with parameter hs color
  have hlocal (index : blockIndex parameter) (root queue : ℤ)
      (hr : |root| ≤ (v7RootCutoff parameter : ℤ)) (hq : |queue| ≤ (queueCutoff parameter : ℤ)) :
      (actualBlockBodyLaw cutoffScale parameter (beta parameter) index root queue).weight color =
        match index with
        | .inl _ => (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).expectation
            (fun source => integerShiftProfile parameter (actualBodyCenter cutoffScale parameter (beta parameter))
              (root + source + queue) color)
        | .inr _ => integerShiftProfile parameter (actualBodyCenter cutoffScale parameter (beta parameter))
            (root + queue) color := by
    cases index with
    | inl leg =>
      simp only [actualBlockBodyLaw, mix_weight, FiniteDist.expectation]
      apply Finset.sum_congr rfl
      intro source _
      have hshift : |root + (source : ℤ) + queue| ≤ (maxBodyShift cutoffScale parameter : ℤ) :=
        actualBodyBranch_shift_bound cutoffScale parameter root queue hr hq (.inr source)
      rw [(hs _ hshift).1]
    | inr body =>
      exact congrFun (hs _ (by simpa only [actualSourceShift, add_zero] using
        actualBodyBranch_shift_bound cutoffScale parameter root queue hr hq (.inl ()))).1 color
  calc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      apply congrArg
      funext sample
      apply congrArg
      funext word
      exact hlocal index _ _ (actualRootField_bound parameter word index)
        (actualQueueShifts_bound parameter sample index)
    _ = _ := actual_body_population_expectation cutoffScale parameter
      (fun shift => integerShiftProfile parameter (actualBodyCenter cutoffScale parameter (beta parameter)) shift color)

theorem actual_endpoint_sum_coordinate (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (color : Fin (Parameters.modulus parameter)) :
    (∑ index : blockIndex parameter, (actualEndpointVector cutoffScale parameter beta index).ofLp color) =
      (Parameters.legs parameter : ℝ) *
        ((∑ second, ((actualActivatedSource cutoffScale parameter).mix
          (actualPairBranch cutoffScale parameter beta)).weight (color, second)) +
         (∑ first, ((actualActivatedSource cutoffScale parameter).mix
          (actualPairBranch cutoffScale parameter beta)).weight (first, color)) -
         2 * (actualReferenceLaw cutoffScale parameter beta).weight color) /
          Real.sqrt ((actualReferenceLaw cutoffScale parameter beta).weight color) := by
  simp only [Fintype.sum_sum_type, actualEndpointVector, whiten_apply, PiLp.zero_apply,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero, add_zero,
    mul_div_assoc]

theorem actual_normalized_mean_coordinate (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (word : actualRootWord parameter) (queue : blockIndex parameter → ℤ)
    (color : Fin (Parameters.modulus parameter)) :
    (actualNormalizedBlockMean cutoffScale parameter beta word queue).ofLp color =
      actualFockScale parameter *
        ((∑ index : blockIndex parameter, (actualBlockBodyLaw cutoffScale parameter beta index
          (actualRootField parameter word index) (queue index)).weight color) -
          (Parameters.bodies parameter : ℝ) * (actualReferenceLaw cutoffScale parameter beta).weight color +
          (Parameters.legs parameter : ℝ) *
            ((∑ second, ((actualActivatedSource cutoffScale parameter).mix
              (actualPairBranch cutoffScale parameter beta)).weight (color, second)) +
             (∑ first, ((actualActivatedSource cutoffScale parameter).mix
              (actualPairBranch cutoffScale parameter beta)).weight (first, color)) -
             2 * (actualReferenceLaw cutoffScale parameter beta).weight color)) /
            Real.sqrt ((actualReferenceLaw cutoffScale parameter beta).weight color) := by
  simp only [actualNormalizedBlockMean, WithLp.ofLp_smul, WithLp.ofLp_sum, WithLp.ofLp_add,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.add_apply, Finset.sum_add_distrib]
  rw [actual_endpoint_sum_coordinate]
  simp only [actualBlockBodyVector, whiten_apply, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, blockIndex_card, nsmul_eq_mul]
  ring

theorem finite_vector_mean_coordinate {Sample Color : Type*} [Fintype Sample] [Fintype Color]
    (law : FiniteDist Sample) (value : Sample → EuclideanSpace ℝ Color) (color : Color) :
    (vectorMean law value).ofLp color = law.expectation (fun sample => (value sample).ofLp color) := by
  simp only [vectorMean, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, FiniteDist.expectation]

/-- The true joint mean is zero after averaging the single shared queue and
the complete zero-sum root word. No independent-root approximation is used. -/
theorem actual_joint_mean_zero_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      vectorMean (FiniteDist.retype (actualQueuePlacementLaw parameter))
        (fun sample => vectorMean (actualRootConditionLaw parameter) (fun word =>
          actualNormalizedBlockMean cutoffScale parameter (beta parameter) word (actualQueueShifts parameter sample))) = 0 := by
  filter_upwards [actual_body_mean_eventually cutoffScale hscale beta hbeta,
    actual_pair_branch_mixture_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_total_mean_eventually cutoffScale hscale] with parameter hb hp hr hc
  have hpopulation : (Parameters.bodies parameter : ℝ) + 2 * Parameters.legs parameter =
      Parameters.dimension parameter := by exact_mod_cast Parameters.population_identity parameter
  ext color
  simp only [finite_vector_mean_coordinate, actual_normalized_mean_coordinate,
    div_eq_mul_inv, expectation_mul_const, expectation_const_mul, expectation_add,
    expectation_sub, expectation_sum, expectation_const, PiLp.zero_apply]
  rw [hb color]
  simp_rw [hp, hr.2.2]
  have hcancel : (Parameters.bodies parameter : ℝ) * actualFullBodyProfile cutoffScale parameter (beta parameter) color -
      Parameters.bodies parameter * actualReferenceMean cutoffScale parameter (beta parameter) color +
      Parameters.legs parameter *
        ((∑ second, localPairMixture cutoffScale parameter (beta parameter) color second) +
          (∑ first, localPairMixture cutoffScale parameter (beta parameter) first color) -
          2 * actualReferenceMean cutoffScale parameter (beta parameter) color) = 0 := by
    have hh := hc (beta parameter) color
    rw [← hpopulation] at hh
    nlinarith only [hh]
  rw [hcancel]
  ring

end
end AFT.V7Calibration

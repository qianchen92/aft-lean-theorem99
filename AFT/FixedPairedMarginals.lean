import AFT.FixedPairedDensity
import AFT.FixedPairedMoments
import AFT.ActualPairMarginals
import AFT.AnchorMean
import AFT.PrimaryLawLower

/-! # Genuine singleton marginal ceilings for the positive four-output law -/

namespace AFT.PhysicalBlockTensors
open scoped BigOperators Classical
noncomputable section

theorem positive_singleton_le_fourOutputCount {Color : Type*} [Fintype Color]
    [decision : DecidableEq (Fin 4)] (mass : (Fin 4 → Color) → ℝ)
    (hn : ∀ word, 0 ≤ mass word) (slot : Fin 4) (output : Color) :
    (∑ word : Fin 4 → Color, if word slot = output then mass word else 0) ≤
      fourOutputCount mass output := by
  have hd : decision = instDecidableEqFin 4 := Subsingleton.elim _ _
  cases hd
  unfold fourOutputCount
  apply Finset.sum_le_sum
  intro word _
  have hind : (if word slot = output then (1 : ℝ) else 0) ≤
      ∑ i : Fin 4, if word i = output then 1 else 0 :=
    Finset.single_le_sum (f := fun i : Fin 4 => if word i = output then (1 : ℝ) else 0) (fun i _ => by positivity) (Finset.mem_univ slot)
  simpa only [mul_ite,mul_one,mul_zero] using mul_le_mul_of_nonneg_left hind (hn word)

end
end AFT.PhysicalBlockTensors

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration PhysicalBlockTensors Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fixedPairedMarginalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem publicChartRaw_primary_pair_le_twice (cutoffScale : ℝ) (parameter : ℕ)
    (primary : FiniteDist (Fin (Parameters.modulus parameter)))
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (hc : ∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second)
    (first second : Fin (Parameters.modulus parameter)) :
    (∑ mark, primary.weight mark * publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second) ≤
      2 * averagedInactivePair cutoffScale parameter first second +
        v7Activation cutoffScale parameter * primary.weight first *
          blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
            (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) first second.val := by
  have ha0 : 0 ≤ v7Activation cutoffScale parameter := by
    unfold v7Activation GaussianSource.activation
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have ha1 : v7Activation cutoffScale parameter ≤ 1 := activation_le_one _ _ _ _
  have hraw0 : 0 ≤ averagedInactivePair cutoffScale parameter first second := by
    unfold averagedInactivePair
    exact Finset.sum_nonneg fun source _ => mul_nonneg (FiniteDist.nonneg _ _) (by
      unfold inactivePairAtSource
      exact div_nonneg (add_nonneg
        (TrimmedSlice.mixedPair_nonneg _ _ _ _ _ _ (FiniteDist.nonneg _) _ _)
        (TrimmedSlice.mixedPair_nonneg _ _ _ _ _ _ (FiniteDist.nonneg _) _ _)) (by norm_num))
  have hdiff (mark) :
      (1-v7Activation cutoffScale parameter) *
        (∑ source, (inactiveLegSource cutoffScale parameter).weight source * conditionalPairAtSource cutoffScale parameter mark source first second) ≤
        2 * averagedInactivePair cutoffScale parameter first second := by
    have hh : (∑ source, (inactiveLegSource cutoffScale parameter).weight source * conditionalPairAtSource cutoffScale parameter mark source first second) ≤
        2 * averagedInactivePair cutoffScale parameter first second := by
      unfold averagedInactivePair
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro source _
      exact (mul_le_mul_of_nonneg_left (conditionalPairAtSource_le_twice cutoffScale parameter mark source first second)
        (FiniteDist.nonneg _ _)).trans_eq (by ring)
    exact (mul_le_mul_of_nonneg_left hh (by linarith)).trans
      ((mul_le_mul_of_nonneg_right (show 1-v7Activation cutoffScale parameter ≤ 1 by linarith)
        (by positivity : 0 ≤ 2*averagedInactivePair cutoffScale parameter first second)).trans_eq (one_mul _))
  simp only [hc,conditionalJointOutput,mul_one,mul_add,Finset.sum_add_distrib]
  apply add_le_add
  · calc
      _ ≤ ∑ mark, primary.weight mark * (2*averagedInactivePair cutoffScale parameter first second) :=
        Finset.sum_le_sum fun mark _ => mul_le_mul_of_nonneg_left (hdiff mark) (primary.nonneg mark)
      _ = _ := by rw [← Finset.sum_mul,primary.sum_one,one_mul]
  · simp only [mul_ite,ite_mul,mul_zero,zero_mul,mul_one,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    exact le_of_eq (by ring)

/-- The activated companion retains its original source blur; the uniform
integer-output anchor bound survives that expectation. -/
theorem actual_blurred_primary_anchor_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ output : ℤ,
      v7Activation cutoffScale parameter * blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)
        (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight output ≤ 386 / Parameters.modulus parameter := by
  filter_upwards [actual_primary_anchor_bound_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta] with parameter hb hl output
  simp only [blurredAnchorMean,blurredAnchorKernel,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ sample, (bodyBlur cutoffScale parameter).weight sample *
        (v7Activation cutoffScale parameter * anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
          (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (output-bodyShift cutoffScale parameter sample)) := by
      simp only [anchorMean,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sample _
      apply Finset.sum_congr rfl
      intro color _
      ring
    _ ≤ ∑ sample, (bodyBlur cutoffScale parameter).weight sample * (386 / Parameters.modulus parameter) := by
      apply Finset.sum_le_sum
      intro sample _
      apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
      rw [hl.1]
      exact hb _
    _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]

/-- Both endpoint counts together have bounded density relative to the
actual primary, including the primary-dependent sign and activated atom. -/
theorem publicChartEndpointMean_primary_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ output,
      (∑ mark, (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark *
        publicChartEndpointMean cutoffScale parameter mark (charts mark) output) ≤
      v7Activation cutoffScale parameter * (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight output +
        394 / Parameters.modulus parameter := by
  filter_upwards [actual_inactive_pair_marginal_eventually cutoffScale hscale,
    actual_blurred_primary_anchor_bound_eventually cutoffScale hscale beta hbeta,
    actual_full_anchor_safe_eventually cutoffScale hscale] with parameter hi ha hm charts hc output
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  have hb := publicChartRaw_primary_pair_le_twice cutoffScale parameter primary charts hc
  have hfirst : (∑ second, ∑ mark, primary.weight mark * publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) output second) ≤
      4 / Parameters.modulus parameter + v7Activation cutoffScale parameter * primary.weight output := by
    apply (Finset.sum_le_sum (fun second _ => hb output second)).trans
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,(hm output).1,mul_one]
    have hh := (averagedInactivePair_marginal_le cutoffScale parameter hi output).1
    simp only [div_eq_mul_inv] at *
    linarith
  have hsecond : (∑ first, ∑ mark, primary.weight mark * publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first output) ≤
      390 / Parameters.modulus parameter := by
    apply (Finset.sum_le_sum (fun first _ => hb first output)).trans
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    have hh := (averagedInactivePair_marginal_le cutoffScale parameter hi output).2
    have hh' := ha output.val
    change v7Activation cutoffScale parameter * (∑ first, primary.weight first *
      blurredAnchorKernel _ _ _ _ first output.val) ≤ _ at hh'
    simp only [mul_assoc, ← Finset.mul_sum, div_eq_mul_inv] at *
    linarith
  have heq : (∑ mark, primary.weight mark * publicChartEndpointMean cutoffScale parameter mark (charts mark) output) =
      (∑ second, ∑ mark, primary.weight mark * publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) output second) +
      (∑ first, ∑ mark, primary.weight mark * publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first output) := by
    simp only [publicChartEndpointMean,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> exact Finset.sum_comm
  rw [heq]
  change _ ≤ v7Activation cutoffScale parameter * primary.weight output + _
  simp only [div_eq_mul_inv] at *
  linarith


/-- Exact first counts for the positive primary mixture, retaining the
source shared between the pair and its attached body. -/
theorem primaryChartTriple_count (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (root queue : ℤ) (primary : FiniteDist (Fin (Parameters.modulus parameter)))
    (output : Fin (Parameters.modulus parameter)) :
    tripleOutputCount (signedChartTriple cutoffScale parameter beta charts root queue primary.weight) output =
      (∑ mark, primary.weight mark * publicChartEndpointMean cutoffScale parameter mark (charts mark) output) +
      ∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source *
        (actualShiftedBodyLaw cutoffScale parameter beta (root + source + queue)).weight output := by
  unfold tripleOutputCount signedChartTriple
  simp only [Finset.sum_mul, mul_assoc]
  have heq (first second) :
      (∑ attached, ∑ mark, primary.weight mark *
        (fixedChartTriple cutoffScale parameter beta mark (charts mark) root queue first second attached *
          ((if first = output then 1 else 0) + (if second = output then 1 else 0) + (if attached = output then 1 else 0)))) =
      ∑ mark, primary.weight mark * ∑ attached,
        fixedChartTriple cutoffScale parameter beta mark (charts mark) root queue first second attached *
          ((if first = output then 1 else 0) + (if second = output then 1 else 0) + (if attached = output then 1 else 0)) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp only [heq]
  rw [sum_pair_mixture]
  simp only [fixedChartTriple_count]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, primary.sum_one, one_mul]

/-- The full positive four-output law has a uniform count ceiling against
its genuine calibrated primary reference. -/
theorem fixedPairedKernel_count_primary_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ attachedRoot compensatorRoot queue : ℤ,
    |attachedRoot| ≤ (v7RootCutoff parameter : ℤ) →
    |compensatorRoot| ≤ (v7RootCutoff parameter : ℤ) →
    |queue| ≤ (queueCutoff parameter : ℤ) → ∀ output,
    fourOutputCount (fun word => ∑ input,
      ((actualPrimaryLaw cutoffScale parameter (beta parameter)).prod (actualBodyLaw cutoffScale parameter (beta parameter))).weight input *
      fixedPairedKernel cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue input word) output ≤
      2048 * (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight output := by
  filter_upwards [publicChartEndpointMean_primary_bound_eventually cutoffScale hscale beta hbeta,
    actual_shifted_body_law_eventually cutoffScale hscale beta hbeta,
    fixed_compensator_masses_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_law_quarter_lower_eventually cutoffScale hscale beta hbeta]
    with parameter he hs hm hb hl hp charts hc ar cr queue har hcr hq output
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let body := actualBodyLaw cutoffScale parameter (beta parameter)
  have hbody (color) : body.weight color ≤ 4 / (Parameters.modulus parameter : ℝ) := by
    change (actualBodyLaw cutoffScale parameter (beta parameter)).weight color ≤ _
    rw [hl.2.1]
    exact (hb.2.1 color).2.trans ((mul_le_mul_of_nonneg_left ((actualCoreLaw_bounds parameter).1 color)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))
  have hcomp := integerShiftProfile_bound parameter body.weight (4 / (Parameters.modulus parameter : ℝ))
    (by positivity) hbody cr output
  have hattached : (∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source *
      (actualShiftedBodyLaw cutoffScale parameter (beta parameter) (ar + source + queue)).weight output) ≤
      4 / (Parameters.modulus parameter : ℝ) := by
    calc
      _ ≤ ∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source *
          (4 / (Parameters.modulus parameter : ℝ)) := by
        apply Finset.sum_le_sum
        intro source _
        exact mul_le_mul_of_nonneg_left
          ((hs _ (actualBodyBranch_shift_bound cutoffScale parameter ar queue har hq (.inr source))).2 output)
          (FiniteDist.nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]
  have hfun : (fun word : Fin 4 → Fin (Parameters.modulus parameter) => ∑ input,
      (primary.prod body).weight input * fixedPairedKernel cutoffScale parameter (beta parameter) charts ar cr queue input word) =
      (fun word => signedChartTriple cutoffScale parameter (beta parameter) charts ar queue primary.weight
        (word 0) (word 1) (word 2) * integerShiftProfile parameter body.weight cr (word 3)) := by
    funext word
    exact fixedPairedKernel_average_factor cutoffScale parameter (beta parameter) charts ar cr queue word
  change fourOutputCount (fun word => ∑ input, (primary.prod body).weight input *
    fixedPairedKernel cutoffScale parameter (beta parameter) charts ar cr queue input word) output ≤ _
  rw [hfun, four_output_product_count, (hm cr hcr).1, mul_one,
    signedChartTriple_total, primary.sum_one, one_mul, primaryChartTriple_count]
  have hend := he charts hc output
  have hact : v7Activation cutoffScale parameter * primary.weight output ≤ primary.weight output :=
    (mul_le_mul_of_nonneg_right (activation_le_one _ _ _ _) (primary.nonneg output)).trans_eq (one_mul _)
  have hpl := hp output
  change 1 / (4 * (Parameters.modulus parameter : ℝ)) ≤ primary.weight output at hpl
  change _ ≤ 2048 * primary.weight output
  change (∑ mark, primary.weight mark * publicChartEndpointMean cutoffScale parameter mark (charts mark) output) ≤
    v7Activation cutoffScale parameter * primary.weight output + _ at hend
  simp only [div_eq_mul_inv, mul_inv_rev] at *
  nlinarith [primary.nonneg output]

/-- Every singleton marginal of the positive physical channel is bounded
before any canonicalization or inverse is applied. -/
theorem fixedPairedKernel_singleton_primary_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ attachedRoot compensatorRoot queue : ℤ,
    |attachedRoot| ≤ (v7RootCutoff parameter : ℤ) →
    |compensatorRoot| ≤ (v7RootCutoff parameter : ℤ) →
    |queue| ≤ (queueCutoff parameter : ℤ) → ∀ (slot : Fin 4) output,
    (∑ word : Fin 4 → Fin (Parameters.modulus parameter), if word slot = output then
      ∑ input, ((actualPrimaryLaw cutoffScale parameter (beta parameter)).prod (actualBodyLaw cutoffScale parameter (beta parameter))).weight input *
        fixedPairedKernel cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue input word else 0) ≤
      2048 * (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight output := by
  filter_upwards [fixedPairedKernel_count_primary_eventually cutoffScale hscale beta hbeta]
    with parameter h charts hc ar cr queue har hcr hq slot output
  apply (positive_singleton_le_fourOutputCount _ (fun word =>
    Finset.sum_nonneg fun input _ => mul_nonneg (FiniteDist.nonneg _ _)
      (fixedPairedKernel_nonneg _ _ _ _ _ _ _ _ _)) slot output).trans
  exact h charts hc ar cr queue har hcr hq output

end
end AFT.V7Calibration

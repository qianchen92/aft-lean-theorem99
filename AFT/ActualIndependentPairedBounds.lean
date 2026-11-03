import AFT.IndependentPairedFibers
import AFT.FixedPairedMarginals
import AFT.FixedPairedPrimaryEnergy
import AFT.ChannelMixedFibers

/-! # Sharp independent-root numerator fibers of the actual physical block -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentBoundsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def fixedPairedPrimaryDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (word : Fin 4 → Fin (Parameters.modulus parameter)) : ℝ :=
  fixedPairedChartRaw cutoffScale parameter beta charts attachedRoot compensatorRoot queue profile word /
    (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter beta)).weight word

/-- The three raw budgets retain the old primary's L2 and fixed fiber
separately. The one-fixed loss is lambda^4, while the sup loss is lambda^8. -/
theorem fixedPairedPrimaryDensity_fibers_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ attachedRoot compensatorRoot queue : ℤ,
      |attachedRoot| ≤ (v7RootCutoff parameter : ℤ) →
      |compensatorRoot| ≤ (v7RootCutoff parameter : ℤ) → |queue| ≤ (queueCutoff parameter : ℤ) →
    ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ color, profile color) = 0 →
    ∀ bound : ℝ, 0 ≤ bound →
      (∀ color, |profile color / (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color| ≤ bound) →
    (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).l2Sq
        (fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile) ≤
        (26912768 * (parameter : ℝ) ^ 8) * profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile ∧
    (∀ slot values, MixedKernel.fiberSq (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))
      (fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile)
      {slot} values ≤ (34816 * 2048 * 773 ^ 2) * (parameter : ℝ) ^ 8 * bound ^ 2) ∧
    (∀ word, |fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile word| ≤
      (34816 * 773) * (parameter : ℝ) ^ 8 * bound) := by
  filter_upwards [fixedPairedChartRaw_primary_energy_eventually cutoffScale hscale beta hbeta,
    fixedPairedKernel_primary_density_eventually cutoffScale hscale beta hbeta,
    fixedPairedKernel_singleton_primary_eventually cutoffScale hscale beta hbeta,
    actual_paired_lift_sup_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta]
    with parameter he hd hm hl hw hp charts hc ar cr queue har hcr hqueue profile hcanonical bound hbound hprofile
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let body := actualBodyLaw cutoffScale parameter (beta parameter)
  let kernel := fixedPairedKernel cutoffScale parameter (beta parameter) charts ar cr queue
  let score := fun input : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) =>
    pairedLift primary.weight body.weight
      (fun color position => publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val)
      (v7Activation cutoffScale parameter) profile input.1 input.2
  have href (slot : Fin 4) (color) : 0 < primary.weight color := by
    change 0 < (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color
    rw [hw.1]
    exact hp.1 color
  have hscore (input) : |score input| ≤ 773 * bound := hl profile bound hbound hprofile input.1 input.2
  have hraw : fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts ar cr queue profile =
      MixedKernel.channelDensity (primary.prod body) (fun _ : Fin 4 => primary) kernel score := by
    funext word
    unfold fixedPairedPrimaryDensity MixedKernel.channelDensity
    congr 1
    exact fixedPairedChartRaw_expectation _ _ _ _ _ _ _ _ _
  refine ⟨?_,?_,?_⟩
  · change densitySquareNorm _ (fun word => _ / _) ≤ _
    rw [densityScore_square]
    exact he charts hc ar cr queue har hqueue profile hcanonical
  · intro slot values
    rw [hraw]
    have hh := MixedKernel.channelDensity_singleton_square_le (primary.prod body)
      (fun _ : Fin 4 => primary) kernel (34816 * (parameter : ℝ) ^ 8) 2048 (773 * bound)
      href (by positivity) (by positivity)
      (fixedPairedKernel_nonneg cutoffScale parameter (beta parameter) charts ar cr queue)
      (hd charts hc ar cr queue har hqueue) (hm charts hc ar cr queue har hcr hqueue)
      score hscore slot values
    exact hh.trans_eq (by ring)
  · intro word
    rw [hraw]
    have hh := signedChannel_density_abs_le (primary.prod body)
      (FiniteDist.independent (fun _ : Fin 4 => primary)).weight kernel
      (34816 * (parameter : ℝ) ^ 8) (773 * bound)
      (fun word => by
        change 0 < ∏ slot : Fin 4, primary.weight (word slot)
        exact Finset.prod_pos fun slot _ => href slot (word slot)) (by positivity)
      (fixedPairedKernel_nonneg cutoffScale parameter (beta parameter) charts ar cr queue)
      (hd charts hc ar cr queue har hqueue) score hscore word
    exact hh.trans_eq (by ring)

end
end AFT.V7Calibration

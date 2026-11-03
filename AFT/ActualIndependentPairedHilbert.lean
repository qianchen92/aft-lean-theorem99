import AFT.ActualIndependentPairedBounds
import AFT.JointSignedChannel

/-! # Sharp physical numerator bounds with arbitrary remaining joint input fibers -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentHilbertFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The actual physical channel retains every other old coordinate inside
one Hilbert space. In particular there is no rank-one decomposition cost. -/
theorem fixedPairedPrimaryDensity_hilbert_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
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
    ∀ (Fiber : Type) [Fintype Fiber], ∀ fiber : FiniteDist Fiber,
    ∀ kernel : Fin (Parameters.modulus parameter) → Fiber → ℝ,
      (∀ rest, ∑ color, (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color * kernel color rest = 0) →
    ∀ squareBound : ℝ, 0 ≤ squareBound →
      (∀ color, fiber.l2Sq (kernel color) ≤ squareBound) →
    (fiber.expectation (fun rest =>
      (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).l2Sq
        (fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue
          (fun color => (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color * kernel color rest))) ≤
      (26912768 * (parameter : ℝ) ^ 8) *
        fiber.expectation (fun rest => (actualPrimaryLaw cutoffScale parameter (beta parameter)).l2Sq (fun color => kernel color rest))) ∧
    (∀ (slot : Fin 4) color,
      (FiniteDist.independent (fun _ : {other : Fin 4 // other ≠ slot} => actualPrimaryLaw cutoffScale parameter (beta parameter))).expectation
        (fun rest => fiber.l2Sq (fun remaining =>
          fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue
            (fun mark => (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark * kernel mark remaining)
            ((Equiv.funSplitAt slot (Fin (Parameters.modulus parameter))).symm (color,rest)))) ≤
      (34816 * 2048 * 1191970) * (parameter : ℝ) ^ 8 * squareBound) ∧
    (∀ word, fiber.l2Sq (fun rest =>
      fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue
        (fun mark => (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark * kernel mark rest) word) ≤
      (34816 ^ 2 * 1191970) * (parameter : ℝ) ^ 16 * squareBound) := by
  filter_upwards [fixedPairedChartRaw_primary_energy_eventually cutoffScale hscale beta hbeta,
    fixedPairedKernel_primary_density_eventually cutoffScale hscale beta hbeta,
    fixedPairedKernel_singleton_primary_eventually cutoffScale hscale beta hbeta,
    actual_paired_lift_hilbert_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta]
    with parameter he hd hm hl hw hp charts hc ar cr queue har hcr hqueue Fiber inst fiber kernel hcanonical squareBound hbound hkernel
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let body := actualBodyLaw cutoffScale parameter (beta parameter)
  let channel := fixedPairedKernel cutoffScale parameter (beta parameter) charts ar cr queue
  let score := fun input : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) =>
    fun rest => pairedLift primary.weight body.weight
      (fun color position => publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val)
      (v7Activation cutoffScale parameter) (fun color => primary.weight color * kernel color rest) input.1 input.2
  have href (slot : Fin 4) (color) : 0 < primary.weight color := by
    change 0 < (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color
    rw [hw.1]
    exact hp.1 color
  have hscore (input) : fiber.l2Sq (score input) ≤ 1191970 * squareBound :=
    hl Fiber fiber kernel squareBound hbound hkernel input.1 input.2
  have hraw (rest) : fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts ar cr queue
      (fun color => primary.weight color * kernel color rest) =
      MixedKernel.channelDensity (primary.prod body) (fun _ : Fin 4 => primary) channel (fun input => score input rest) := by
    funext word
    unfold fixedPairedPrimaryDensity MixedKernel.channelDensity
    congr 1
    exact fixedPairedChartRaw_expectation _ _ _ _ _ _ _ _ _
  have hrawpoint (rest word) := congrFun (hraw rest) word
  dsimp only [primary] at hrawpoint
  refine ⟨?_,?_,?_⟩
  · change (∑ rest, fiber.weight rest * _) ≤ _
    rw [FiniteDist.expectation, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro rest _
    have hh := he charts hc ar cr queue har hqueue
      (fun color => primary.weight color * kernel color rest) (hcanonical rest)
    rw [profileSquareNorm_weight_mul primary] at hh
    have heq : (FiniteDist.independent (fun _ : Fin 4 => primary)).l2Sq
        (fixedPairedPrimaryDensity cutoffScale parameter (beta parameter) charts ar cr queue
          (fun color => primary.weight color * kernel color rest)) =
        profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => primary)).weight
          (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts ar cr queue
            (fun color => primary.weight color * kernel color rest)) := by
      change densitySquareNorm _ (fun word => _ / _) = _
      exact densityScore_square _ _
    rw [← heq] at hh
    exact (mul_le_mul_of_nonneg_left hh (fiber.nonneg rest)).trans_eq (by ring)
  · intro slot color
    simp_rw [hrawpoint]
    have hh := MixedKernel.channelDensity_singleton_hilbert_square_le (primary.prod body)
      (fun _ : Fin 4 => primary) fiber channel (34816 * (parameter : ℝ) ^ 8) 2048 (1191970 * squareBound)
      href (by positivity) (by positivity)
      (fixedPairedKernel_nonneg cutoffScale parameter (beta parameter) charts ar cr queue)
      (hd charts hc ar cr queue har hqueue) (hm charts hc ar cr queue har hcr hqueue)
      score hscore slot color
    exact hh.trans_eq (by ring)
  · intro word
    simp_rw [hrawpoint]
    have hh := signedChannel_density_hilbert_square_le (primary.prod body) fiber
      (fun input => channel input word) ((FiniteDist.independent (fun _ : Fin 4 => primary)).weight word)
      (34816 * (parameter : ℝ) ^ 8) (1191970 * squareBound)
      (by change 0 < ∏ slot : Fin 4, primary.weight (word slot); exact Finset.prod_pos fun slot _ => href slot (word slot))
      (by positivity) (by positivity)
      (fun input => fixedPairedKernel_nonneg _ _ _ _ _ _ _ input word)
      (hd charts hc ar cr queue har hqueue word) score hscore
    exact hh.trans_eq (by ring)

end
end AFT.V7Calibration

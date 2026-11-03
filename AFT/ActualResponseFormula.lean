import AFT.V7ActualProjection
import AFT.AnchorSeed

/-! # The physical blurred-anchor formula and mass of the actual response -/

namespace AFT

noncomputable section

namespace V7Calibration

open GaussianSource Filter
open scoped BigOperators Classical Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The averaged finite translation matrix is literally the difference
of its two physical blurred anchor kernels. -/
theorem anchorError_apply_formula {σ : Type*} [Fintype σ]
    (parameter : ℕ) (bodyShift sourceShift : σ → ℤ) (law : FiniteDist σ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    anchorError parameter bodyShift sourceShift law profile output =
      ∑ color, profile color *
        (blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) bodyShift law color output.val -
          blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) sourceShift law color output.val) := by
  have heq (sample : σ × Bool) (color : Fin (Parameters.modulus parameter)) :
      errorStarts parameter sourceShift sample color + errorShift bodyShift sourceShift sample =
        publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color sample.2 + bodyShift sample.1 := by
    unfold errorStarts errorShift
    ring
  unfold anchorError averagedIntervalTranslationOperator
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ sample : σ × Bool, (errorLaw law).weight sample *
    ∑ color, intervalAnchorDifference (errorStarts parameter sourceShift sample)
      (errorShift bodyShift sourceShift sample) (Parameters.anchorWidth parameter) color output.val * profile color) = _
  simp only [intervalAnchorDifference]
  simp_rw [heq]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro color _
  simp only [errorStarts, errorLaw, Fintype.sum_prod_type, FiniteDist.prod_weight,
    FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool,
    blurredAnchorKernel, publicAnchorKernel_translate, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample _
  ring

/-- Independent unused randomness disappears from a physical blur exactly. -/
theorem blurredAnchorKernel_ignore_right {α β : Type*} [Fintype α] [Fintype β]
    (modulus width : ℕ) (shift : α → ℤ) (first : FiniteDist α) (second : FiniteDist β)
    (color : Fin modulus) (output : ℤ) :
    blurredAnchorKernel modulus width (fun sample : α × β => shift sample.1) (first.prod second) color output =
      blurredAnchorKernel modulus width shift first color output := by
  simp only [blurredAnchorKernel, Fintype.sum_prod_type, FiniteDist.prod_weight]
  apply Finset.sum_congr rfl
  intro sample _
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, second.sum_one, one_mul]

end V7Calibration

namespace GaussianSource

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open V7Calibration Filter
open scoped BigOperators Classical Topology

/-- The concrete response keeps calibration's leg source separate from the
root-only compensator. -/
theorem actualResponse_apply_formula (cutoffScale : ℝ) (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    actualResponse cutoffScale parameter profile output = profile output +
      (v7Activation cutoffScale parameter)⁻¹ *
        (∑ color, paletteSign (Parameters.modulus parameter) color * profile color) *
        signResponse parameter cutoffScale (boundaryHalf cutoffScale parameter)
          (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
          (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter) output +
      ∑ color, profile color *
        (blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
          (fun sample => bodyShift cutoffScale parameter sample.1) (pairSourceLaw cutoffScale parameter) color output.val -
         blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
          (compensatorRootShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter) color output.val) := by
  simp only [actualResponse, responseOperator, LinearMap.add_apply, Pi.add_apply, primaryRankOperator_apply,
    Pi.smul_apply, smul_eq_mul, profileSignMap, LinearMap.coe_mk, AddHom.coe_mk, signFunctional,
    anchorError_apply_formula]


/-- Expanded physical response, with the true body blur and only the root
marginal on the independent compensation branch. -/
theorem actualResponse_physical_formula (cutoffScale : ℝ) (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    actualResponse cutoffScale parameter profile output = profile output +
      (v7Activation cutoffScale parameter)⁻¹ *
        (∑ color, paletteSign (Parameters.modulus parameter) color * profile color) *
        signResponse parameter cutoffScale (boundaryHalf cutoffScale parameter)
          (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
          (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter) output +
      blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) profile output.val -
      blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)) profile output.val := by
  rw [actualResponse_apply_formula]
  have hbody (color : Fin (Parameters.modulus parameter)) :
      blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (fun sample => bodyShift cutoffScale parameter sample.1) (pairSourceLaw cutoffScale parameter) color output.val =
      blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) color output.val :=
    blurredAnchorKernel_ignore_right _ _ _ _ _ _ _
  have hroot (color : Fin (Parameters.modulus parameter)) :
      blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (compensatorRootShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter) color output.val =
      blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)) color output.val := by
    exact (blurredAnchorKernel_ignore_right (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (fun sample : bodySample cutoffScale parameter => (sample.1 : ℤ)) (bodyBlur cutoffScale parameter)
      (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)) color output.val).trans
      (blurredAnchorKernel_ignore_right (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)) (extraBlur cutoffScale parameter) color output.val)

  simp only [hbody, hroot, mul_sub, Finset.sum_sub_distrib, blurredAnchorMean]
  ring

/-- The actual inverse preserves total mass, since both anchor laws have
mass one and the calibrated sign response has mass zero. -/
theorem actualResponse_mass_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter in atTop, ∀ profile : Fin (Parameters.modulus parameter) → ℝ,
      (∑ output, actualResponse cutoffScale parameter profile output) = ∑ color, profile color := by
  have hsign := base_sign_estimates_eventually cutoffScale hscale (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale)
    ((actual_physical_supports_eventually cutoffScale hscale).mono fun _ h => h.1)
  filter_upwards [hsign, actual_anchor_margin_eventually cutoffScale hscale] with parameter hs hm profile
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two parameter; omega)
  have hbody (color : Fin (Parameters.modulus parameter)) :=
    (blurredAnchorKernel_safe_mass (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (Parameters.safeMargin parameter) (fun sample => bodyShift cutoffScale parameter sample.1)
      (pairSourceLaw cutoffScale parameter) hw (Parameters.anchor_clearance parameter) (by positivity) hm.1 color).1
  have hroot (color : Fin (Parameters.modulus parameter)) :=
    (blurredAnchorKernel_safe_mass (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (Parameters.safeMargin parameter) (compensatorRootShift cutoffScale parameter)
      (pairSourceLaw cutoffScale parameter) hw (Parameters.anchor_clearance parameter) (by positivity) hm.2 color).1
  simp only [actualResponse_apply_formula, Finset.sum_add_distrib, ← Finset.mul_sum, hs.2.2.2, mul_zero, add_zero]
  have he : (∑ output : Fin (Parameters.modulus parameter), ∑ color, profile color *
      (blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (fun sample => bodyShift cutoffScale parameter sample.1) (pairSourceLaw cutoffScale parameter) color output.val -
       blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (compensatorRootShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter) color output.val)) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, hbody, hroot, sub_self, mul_zero, Finset.sum_const_zero]
  rw [he, add_zero]

theorem actualResponse_inverse_mass_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter in atTop,
      ∀ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
      operator.toLinearMap = actualResponse cutoffScale parameter →
      ∀ profile, (∑ color, operator.symm profile color) = ∑ color, profile color := by
  filter_upwards [actualResponse_mass_eventually cutoffScale hscale] with parameter hm operator hop profile
  have hh := hm (operator.symm profile)
  rw [← hop] at hh
  simpa only [LinearEquiv.coe_coe, operator.apply_symm_apply] using hh.symm

end GaussianSource
end
end AFT

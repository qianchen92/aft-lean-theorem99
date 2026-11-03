import AFT.ActualPairedLiftSharp
import AFT.FixedPairedPrimaryDensity
import AFT.SignedChannelFibers

/-! # The true paired lift preserves old fixed-primary fibers -/

namespace AFT
open scoped BigOperators Classical
noncomputable section

/-- The anchor term costs its actual average density, rather than a
worst-case row summed over the palette. -/
theorem pairedLift_sup_le {Primary Body : Type*} [Fintype Primary]
    (primary : Primary → ℝ) (body : Body → ℝ) (anchor : Primary → Body → ℝ)
    (activation comparison bound : ℝ) (profile : Primary → ℝ)
    (hp : ∀ color, 0 < primary color) (hb : ∀ center, 0 ≤ body center)
    (ha : ∀ color center, 0 ≤ anchor color center)
    (hactivation : 0 ≤ activation) (hcomparison : 0 ≤ comparison) (hbound : 0 ≤ bound)
    (hcompare : ∀ center, activation * applyAnchor anchor primary center ≤ comparison * body center)
    (hprofile : ∀ color, |profile color / primary color| ≤ bound)
    (color : Primary) (center : Body) :
    |pairedLift primary body anchor activation profile color center| ≤ (1 + comparison) * bound := by
  have hprofile' (color) : |profile color| ≤ bound * primary color := by
    have hh := hprofile color
    rw [abs_div, abs_of_pos (hp color)] at hh
    exact (div_le_iff₀ (hp color)).mp hh
  have hanchor : |applyAnchor anchor profile center| ≤
      bound * applyAnchor anchor primary center := by
    unfold applyAnchor
    calc
      _ ≤ ∑ color, |anchor color center * profile color| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ color, bound * (anchor color center * primary color) := by
        apply Finset.sum_le_sum
        intro color _
        rw [abs_mul, abs_of_nonneg (ha color center)]
        exact (mul_le_mul_of_nonneg_left (hprofile' color) (ha color center)).trans_eq (by ring)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcomp : |activation * applyAnchor anchor profile center / body center| ≤ comparison * bound := by
    by_cases hz : body center = 0
    · simp only [hz, div_zero, abs_zero]
      exact mul_nonneg hcomparison hbound
    · have hbody : 0 < body center := lt_of_le_of_ne (hb center) (Ne.symm hz)
      rw [abs_div, abs_mul, abs_of_nonneg hactivation, abs_of_pos hbody]
      apply (div_le_iff₀ hbody).mpr
      calc
        _ ≤ activation * (bound * applyAnchor anchor primary center) :=
          mul_le_mul_of_nonneg_left hanchor hactivation
        _ = bound * (activation * applyAnchor anchor primary center) := by ring
        _ ≤ bound * (comparison * body center) := mul_le_mul_of_nonneg_left (hcompare center) hbound
        _ = _ := by ring
  exact (abs_sub (profile color / primary color)
    (activation * applyAnchor anchor profile center / body center)).trans
    ((add_le_add (hprofile color) hcomp).trans_eq (by ring))

/-- A whole remaining joint input fiber is retained in the compensated
score; the constant has no dependence on that fiber's dimension. -/
theorem pairedLift_hilbert_sup_square_le {Primary Body Fiber : Type*}
    [Fintype Primary] [Fintype Fiber]
    (primary : Primary → ℝ) (body : Body → ℝ) (anchor : Primary → Body → ℝ)
    (activation comparison squareBound : ℝ) (fiber : FiniteDist Fiber)
    (kernel : Primary → Fiber → ℝ)
    (hp : ∀ color, 0 < primary color) (hb : ∀ center, 0 ≤ body center)
    (ha : ∀ color center, 0 ≤ anchor color center)
    (hactivation : 0 ≤ activation) (hcomparison : 0 ≤ comparison) (hbound : 0 ≤ squareBound)
    (hcompare : ∀ center, activation * applyAnchor anchor primary center ≤ comparison * body center)
    (hkernel : ∀ color, fiber.l2Sq (kernel color) ≤ squareBound)
    (color : Primary) (center : Body) :
    fiber.l2Sq (fun rest => pairedLift primary body anchor activation
      (fun mark => primary mark * kernel mark rest) color center) ≤
      (2 * (1 + comparison ^ 2)) * squareBound := by
  let weight : Primary → ℝ := fun mark => activation * anchor mark center * primary mark / body center
  have hw (mark) : 0 ≤ weight mark := div_nonneg
    (mul_nonneg (mul_nonneg hactivation (ha mark center)) (hp mark).le) (hb center)
  have hmass : (∑ mark, weight mark) ≤ comparison := by
    by_cases hz : body center = 0
    · simpa only [weight, hz, div_zero, Finset.sum_const_zero] using hcomparison
    · have hbody : 0 < body center := lt_of_le_of_ne (hb center) (Ne.symm hz)
      unfold weight
      rw [← Finset.sum_div]
      apply (div_le_iff₀ hbody).mpr
      simpa only [applyAnchor, Finset.mul_sum, mul_assoc] using hcompare center
  have hm0 : 0 ≤ ∑ mark, weight mark := Finset.sum_nonneg fun mark _ => hw mark
  have hc := positiveCombination_l2Sq_le fiber weight kernel squareBound hw hkernel
  have hc' : fiber.l2Sq (fun rest => ∑ mark, weight mark * kernel mark rest) ≤ comparison ^ 2 * squareBound :=
    hc.trans (mul_le_mul_of_nonneg_right ((sq_le_sq₀ hm0 hcomparison).mpr hmass) hbound)
  have heq (rest) : pairedLift primary body anchor activation
      (fun mark => primary mark * kernel mark rest) color center =
      kernel color rest - ∑ mark, weight mark * kernel mark rest := by
    unfold pairedLift applyAnchor weight
    rw [mul_div_cancel_left₀ _ (hp color).ne']
    congr 1
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro mark _
    ring
  have hpoint (rest) : (kernel color rest - ∑ mark, weight mark * kernel mark rest) ^ 2 ≤
      2 * kernel color rest ^ 2 + 2 * (∑ mark, weight mark * kernel mark rest) ^ 2 := by
    nlinarith [sq_nonneg (kernel color rest + ∑ mark, weight mark * kernel mark rest)]
  calc
    _ ≤ 2 * fiber.l2Sq (kernel color) +
        2 * fiber.l2Sq (fun rest => ∑ mark, weight mark * kernel mark rest) := by
      simp only [FiniteDist.l2Sq, FiniteDist.expectation, heq]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro rest _
      exact (mul_le_mul_of_nonneg_left (hpoint rest) (fiber.nonneg rest)).trans_eq (by ring)
    _ ≤ 2 * squareBound + 2 * (comparison ^ 2 * squareBound) := by linarith [hkernel color]
    _ = _ := by ring

namespace V7Calibration
open GaussianSource Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true activated anchor average is bounded by the actual safe body
probability, including its zero-mass exterior. -/
theorem actual_anchor_primary_body_comparison_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ center : Fin (Parameters.modulus parameter),
      v7Activation cutoffScale parameter *
        applyAnchor (fun color position => publicAnchorKernel (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color position.val)
          (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight center ≤
        772 * (actualBodyLaw cutoffScale parameter (beta parameter)).weight center := by
  filter_upwards [actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_anchor_bound_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hl hb hmean hparameter
  let anchor := fun color position : Fin (Parameters.modulus parameter) =>
    publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let body := actualBodyLaw cutoffScale parameter (beta parameter)
  let a := v7Activation cutoffScale parameter
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hcompare (center : Fin (Parameters.modulus parameter)) :
      a * applyAnchor anchor primary.weight center ≤ 772 * body.weight center := by
    by_cases hc : center ∈ safePalette parameter
    · have hbody : 1 / (2 * (Parameters.modulus parameter : ℝ)) ≤ body.weight center := by
        change _ ≤ (actualBodyLaw cutoffScale parameter (beta parameter)).weight center
        rw [hl.2.1]
        have hh := (div_le_div_of_nonneg_right ((actualCoreLaw_bounds parameter).2 center hc)
          (by norm_num : (0 : ℝ) ≤ 2)).trans (hb.2.1 center).1
        convert hh using 1
        ring
      have hanchor : a * applyAnchor anchor primary.weight center ≤ 386 / Parameters.modulus parameter := by
        change a * applyAnchor anchor (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight center ≤ _
        rw [hl.1]
        simpa only [a, anchor, applyAnchor, anchorMean, mul_comm] using hmean center.val
      exact hanchor.trans ((mul_le_mul_of_nonneg_left hbody
        (by norm_num : (0 : ℝ) ≤ 772)).trans' (by ring_nf; exact le_rfl))
    · have hh : applyAnchor anchor primary.weight center = 0 := by
        unfold applyAnchor
        apply Finset.sum_eq_zero
        intro color _
        change publicAnchorKernel _ _ color center.val * _ = 0
        rw [(actual_anchor_safe_mass parameter color).2 center hc, zero_mul]
      rw [hh, mul_zero]
      exact mul_nonneg (by norm_num) (body.nonneg center)
  exact hcompare

/-- The actual calibrated paired lift has a constant sup norm on density
scores, uniformly over all safe and impossible compensator centers. -/
theorem actual_paired_lift_sup_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ profile : Fin (Parameters.modulus parameter) → ℝ,
      ∀ bound : ℝ, 0 ≤ bound →
      (∀ color, |profile color / (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color| ≤ bound) →
      ∀ color center,
      |pairedLift (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight
        (actualBodyLaw cutoffScale parameter (beta parameter)).weight
        (fun color position => publicAnchorKernel (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color position.val)
        (v7Activation cutoffScale parameter) profile color center| ≤ 773 * bound := by
  filter_upwards [actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_anchor_bound_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hl hp hb hmean hparameter
  let anchor := fun color position : Fin (Parameters.modulus parameter) =>
    publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let body := actualBodyLaw cutoffScale parameter (beta parameter)
  let a := v7Activation cutoffScale parameter
  have ha : 0 ≤ a := by
    unfold a v7Activation GaussianSource.activation
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hp0 (color) : 0 < primary.weight color := by rw [show primary.weight = _ from hl.1]; exact hp.1 color
  have hcompare (center : Fin (Parameters.modulus parameter)) :
      a * applyAnchor anchor primary.weight center ≤ 772 * body.weight center := by
    by_cases hc : center ∈ safePalette parameter
    · have hbody : 1 / (2 * (Parameters.modulus parameter : ℝ)) ≤ body.weight center := by
        change _ ≤ (actualBodyLaw cutoffScale parameter (beta parameter)).weight center
        rw [hl.2.1]
        have hh := (div_le_div_of_nonneg_right ((actualCoreLaw_bounds parameter).2 center hc)
          (by norm_num : (0 : ℝ) ≤ 2)).trans (hb.2.1 center).1
        convert hh using 1
        ring
      have hanchor : a * applyAnchor anchor primary.weight center ≤ 386 / Parameters.modulus parameter := by
        change a * applyAnchor anchor (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight center ≤ _
        rw [hl.1]
        simpa only [a, anchor, applyAnchor, anchorMean, mul_comm] using hmean center.val
      exact hanchor.trans ((mul_le_mul_of_nonneg_left hbody
        (by norm_num : (0 : ℝ) ≤ 772)).trans' (by ring_nf; exact le_rfl))
    · have hh : applyAnchor anchor primary.weight center = 0 := by
        unfold applyAnchor
        apply Finset.sum_eq_zero
        intro color _
        change publicAnchorKernel _ _ color center.val * _ = 0
        rw [(actual_anchor_safe_mass parameter color).2 center hc, zero_mul]
      rw [hh, mul_zero]
      exact mul_nonneg (by norm_num) (body.nonneg center)
  intro profile bound hbound hprofile color center
  simpa only [show (1 : ℝ) + 772 = 773 by norm_num] using
    pairedLift_sup_le primary.weight body.weight anchor a 772 bound profile hp0 body.nonneg
      (fun color position => publicAnchorKernel_nonneg _ _ _ _) ha (by norm_num) hbound
      hcompare hprofile color center

/-- The sharp sup-fiber lift estimate applies to arbitrary joint kernels
with any finite Hilbert-valued remainder, not just scalar or rank-one inputs. -/
theorem actual_paired_lift_hilbert_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ (Fiber : Type) [Fintype Fiber], ∀ fiber : FiniteDist Fiber,
      ∀ kernel : Fin (Parameters.modulus parameter) → Fiber → ℝ,
      ∀ squareBound : ℝ, 0 ≤ squareBound →
      (∀ color, fiber.l2Sq (kernel color) ≤ squareBound) →
      ∀ color center,
      fiber.l2Sq (fun rest => pairedLift (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight
        (actualBodyLaw cutoffScale parameter (beta parameter)).weight
        (fun color position => publicAnchorKernel (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color position.val)
        (v7Activation cutoffScale parameter)
        (fun mark => (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark * kernel mark rest)
        color center) ≤ 1191970 * squareBound := by
  filter_upwards [actual_anchor_primary_body_comparison_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta]
    with parameter hcompare hl hp
  intro Fiber inst fiber kernel squareBound hbound hkernel color center
  have ha : 0 ≤ v7Activation cutoffScale parameter := by
    unfold v7Activation GaussianSource.activation
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have hh := pairedLift_hilbert_sup_square_le
    (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight
    (actualBodyLaw cutoffScale parameter (beta parameter)).weight
    (fun color position => publicAnchorKernel (Parameters.modulus parameter)
      (Parameters.anchorWidth parameter) color position.val)
    (v7Activation cutoffScale parameter) 772 squareBound fiber kernel
    (fun color => by rw [hl.1]; exact hp.1 color)
    (actualBodyLaw cutoffScale parameter (beta parameter)).nonneg
    (fun color position => publicAnchorKernel_nonneg _ _ _ _) ha (by norm_num) hbound
    hcompare hkernel color center
  norm_num only [show (2 : ℝ) * (1 + 772 ^ 2) = 1191970 by norm_num] at hh
  exact hh

end V7Calibration
end
end AFT

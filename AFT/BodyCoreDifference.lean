import AFT.BodyCentered

/-! # The small safe compensation retained in a body-type input -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem actual_body_core_square (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hp : ∀ color, 0 ≤ actualPrimary cutoffScale parameter beta color)
    (hpm : ∑ color, actualPrimary cutoffScale parameter beta color = 1)
    (hbody : ∀ color, (actualCoreLaw parameter).weight color / 2 ≤ actualBodyCenter cutoffScale parameter beta color)
    (hs : ∀ color, color ∉ safePalette parameter → actualBodyCenter cutoffScale parameter beta color = 0) :
    profileSquareNorm (actualBodyCenter cutoffScale parameter beta)
      (actualBodyCenter cutoffScale parameter beta - (actualCoreLaw parameter).weight) ≤
      bodyCompensation parameter cutoffScale ^ 2 *
        (8 + 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) := by
  let p := actualPrimary cutoffScale parameter beta
  let P := actualBodyCenter cutoffScale parameter beta
  let core := (actualCoreLaw parameter).weight
  let anchor : Fin (Parameters.modulus parameter) → ℝ := fun color =>
    anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) p color.val
  let delta := bodyCompensation parameter cutoffScale
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hanchor0 (color) : 0 ≤ anchor color := Finset.sum_nonneg fun input _ =>
    mul_nonneg (hp input) (publicAnchorKernel_nonneg _ _ _ _)
  have hanchor1 : ∑ color, anchor color = 1 := by
    dsimp only [anchor, anchorMean]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (actual_anchor_safe_mass parameter _).1, mul_one]
    exact hpm
  have hanchorUpper (color) : anchor color ≤ 1 / (Parameters.anchorWidth parameter : ℝ) := by
    calc
      _ ≤ ∑ input, p input * (1 / (Parameters.anchorWidth parameter : ℝ)) := by
        apply Finset.sum_le_sum
        intro input _
        simpa only [one_div] using mul_le_mul_of_nonneg_left (publicAnchorKernel_le (Parameters.modulus parameter) (Parameters.anchorWidth parameter) input color.val) (hp input)
      _ = _ := by rw [← Finset.sum_mul, hpm, one_mul]
  have hcount := probability_difference_counting_sq core anchor
    (2 / (Parameters.modulus parameter : ℝ)) (1 / (Parameters.anchorWidth parameter : ℝ))
    (actualCoreLaw parameter).nonneg hanchor0 (actualCoreLaw parameter).sum_one hanchor1
    (actualCoreLaw_bounds parameter).1 hanchorUpper
  have hlower (color) (hc : color ∈ safePalette parameter) :
      1 / (2 * (Parameters.modulus parameter : ℝ)) ≤ P color := by
    have hh := (actualCoreLaw_bounds parameter).2 color hc
    have hb := hbody color
    dsimp only [P]
    simp only [div_eq_mul_inv, mul_inv_rev] at *
    norm_num at *
    linarith
  have hout (color) (hc : color ∉ safePalette parameter) : (P - core) color = 0 := by
    simp only [P, core, Pi.sub_apply, hs color hc, actualCoreLaw_outside_value parameter color hc, sub_self]
  have heq (color) : (P - core) color = delta * (core color - anchor color) := by
    dsimp only [P, core, delta, anchor, p, Pi.sub_apply, actualBodyCenter, calibratedBodyProfile,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hh := profileSquareNorm_le_counting P (P - core) (safePalette parameter)
    (1 / (2 * (Parameters.modulus parameter : ℝ))) (by positivity) hlower hout
  simp_rw [heq, mul_pow] at hh
  rw [← Finset.mul_sum] at hh
  have hb := mul_le_mul_of_nonneg_left hcount (sq_nonneg delta)
  have hhh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (1 / (2 * (Parameters.modulus parameter : ℝ)))⁻¹)
  apply hh.trans (hhh.trans_eq ?_)
  dsimp only [delta]
  field_simp
  ring

theorem actual_body_core_relative (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hbody : ∀ color, (actualCoreLaw parameter).weight color / 2 ≤ actualBodyCenter cutoffScale parameter beta color ∧
      actualBodyCenter cutoffScale parameter beta color ≤ 2 * (actualCoreLaw parameter).weight color)
    (color : Fin (Parameters.modulus parameter)) :
    |actualBodyCenter cutoffScale parameter beta color - (actualCoreLaw parameter).weight color| ≤
      actualBodyCenter cutoffScale parameter beta color := by
  have hc := (actualCoreLaw parameter).nonneg color
  have hb := hbody color
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith⟩

theorem actual_body_canonical_input_square (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ)
    (hpm : ∑ color, actualPrimary cutoffScale parameter beta color = 1)
    (hp : ∀ color, 0 ≤ actualPrimary cutoffScale parameter beta color)
    (hm : ∑ color, actualBodyCenter cutoffScale parameter beta color = 1)
    (hbody : ∀ color, (actualCoreLaw parameter).weight color / 2 ≤ actualBodyCenter cutoffScale parameter beta color ∧
      actualBodyCenter cutoffScale parameter beta color ≤ 2 * (actualCoreLaw parameter).weight color)
    (hs : ∀ color, color ∉ safePalette parameter → actualBodyCenter cutoffScale parameter beta color = 0)
    (hinside : profileSquareNorm (actualBodyCenter cutoffScale parameter beta)
      (bodyInside parameter (actualBodyCenter cutoffScale parameter beta) shift) ≤
        96 * (shift.natAbs : ℝ) / Parameters.modulus parameter) :
    (∀ color, |bodyCanonicalInput cutoffScale parameter beta shift color| ≤ 5 * actualBodyCenter cutoffScale parameter beta color) ∧
    profileSquareNorm (actualBodyCenter cutoffScale parameter beta) (bodyCanonicalInput cutoffScale parameter beta shift) ≤
      192 * (shift.natAbs : ℝ) / Parameters.modulus parameter +
        2 * bodyCompensation parameter cutoffScale ^ 2 * (8 + 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) := by
  let P := actualBodyCenter cutoffScale parameter beta
  let core := (actualCoreLaw parameter).weight
  let inside := bodyInside parameter P shift
  let mu := bodyOutsideMass parameter P shift
  have hn (color) : 0 ≤ P color := (div_nonneg ((actualCoreLaw parameter).nonneg color) (by norm_num)).trans (hbody color).1
  have hmu := bodyOutsideMass_bounds parameter P hn hm shift
  have hmu0 : 0 ≤ 1 - mu := by dsimp only [mu]; linarith [hmu.2]
  have hmu1 : 1 - mu ≤ 1 := by dsimp only [mu]; linarith [hmu.1]
  have hcore := actual_body_core_square cutoffScale parameter beta hp hpm (fun color => (hbody color).1) hs
  refine ⟨?_, ?_⟩
  · intro color
    change |inside color + (1 - mu) * (P color - core color)| ≤ _
    have hh := actual_body_core_relative cutoffScale parameter beta hbody color
    have hi := bodyInside_relative parameter P hm hbody shift color
    have hc := mul_le_mul_of_nonneg_left hh hmu0
    have hc' := mul_le_mul_of_nonneg_right hmu1 (hn color)
    exact (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hmu0]; change _ ≤ 5 * P color; dsimp only [P, core, inside] at *; nlinarith)
  · have hscale : profileSquareNorm P (-(1 - mu) • (P - core)) ≤ profileSquareNorm P (P - core) := by
      unfold profileSquareNorm
      apply Finset.sum_le_sum
      intro color _
      change ((-(1 - mu)) * (P color - core color))^2 / P color ≤ (P color - core color)^2 / P color
      apply div_le_div_of_nonneg_right _ (hn color)
      have hsq : (-(1 - mu))^2 ≤ 1 := by nlinarith
      simpa only [mul_pow, one_mul] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (P color - core color))
    have heq : bodyCanonicalInput cutoffScale parameter beta shift = inside - (-(1 - mu) • (P - core)) := by
      funext color
      simp only [bodyCanonicalInput, inside, mu, P, core, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    have hh := profileSquareNorm_sub_le_two P inside (-(1 - mu) • (P - core)) hn
    change profileSquareNorm P inside ≤ _ at hinside
    change profileSquareNorm P (P - core) ≤ _ at hcore
    simp only [div_eq_mul_inv] at hinside hcore ⊢
    nlinarith

end
end AFT.V7Calibration

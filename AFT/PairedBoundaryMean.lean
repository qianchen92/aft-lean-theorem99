import AFT.PairedScoreOutput
import AFT.PrimaryLawLower
import AFT.BoundaryCentering
import AFT.FiniteExpectationAlgebra

/-! # Conditional means of the actual public paired score -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color Center : Type*} [Fintype Color] [Fintype Center]

/-- Integrating the compensating center removes its centered anchor term
before any boundary conditioning. Impossible body atoms cause no division assumption. -/
theorem pairedLift_body_expectation (primary : Color → ℝ) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ) (profile : Color → ℝ)
    (hanchor : ∀ color, ∑ center, anchor color center = 1)
    (hsupport : ∀ center, body.weight center = 0 → applyAnchor anchor profile center = 0)
    (hcanonical : ∑ color, profile color = 0) (color : Color) :
    body.expectation (pairedLift primary body.weight anchor activation profile color) = profile color / primary color := by
  have hc (center) : body.weight center *
      (activation * applyAnchor anchor profile center / body.weight center) =
      activation * applyAnchor anchor profile center := by
    by_cases hz : body.weight center = 0
    · simp only [hz, hsupport center hz, mul_zero, zero_div]
    · exact mul_div_cancel₀ _ hz
  unfold FiniteDist.expectation pairedLift
  simp only [mul_sub, Finset.sum_sub_distrib, hc, ← Finset.sum_mul,
    ← Finset.mul_sum, body.sum_one, one_mul, applyAnchor_mass anchor profile hanchor,
    hcanonical, mul_zero, sub_zero]

/-- The genuine primary/compensator public score has exact zero mean in
each boundary-record cell, not merely before the record is observed. -/
theorem pairedLift_boundary_mean_zero (primary : FiniteDist Color) (body : FiniteDist Center)
    (anchor : Color → Center → ℝ) (activation : ℝ) (profile : Color → ℝ)
    (hprimary : ∀ color, primary.weight color ≠ 0)
    (hanchor : ∀ color, ∑ center, anchor color center = 1)
    (hsupport : ∀ center, body.weight center = 0 → applyAnchor anchor profile center = 0)
    (interior : Finset Color) (hcanonical : ∑ color, profile color = 0)
    (houtside : ∀ color ∉ interior, profile color = 0)
    (record : Option Color)
    (hpos : 0 < primary.eventMass (fun color => FiniteDist.boundaryRecord interior color = record)) :
    ((primary.condition (fun color => FiniteDist.boundaryRecord interior color = record) hpos).prod body).expectation
      (fun pair => pairedLift primary.weight body.weight anchor activation profile pair.1 pair.2) = 0 := by
  rw [FiniteDist.expectation_prod]
  simp only [pairedLift_body_expectation primary.weight body anchor activation profile hanchor hsupport hcanonical]
  apply FiniteDist.boundary_condition_centered primary interior record hpos
  · exact (densityScore_mass primary.weight profile hprimary).trans hcanonical
  · intro color hc
    simp only [houtside color hc, zero_div]

end
end AFT

namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero

/-- The actual safe anchor and actual body support discharge every
hypothesis of conditional paired centering. -/
theorem actual_paired_boundary_mean_zero_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ profile : Fin (Parameters.modulus n) → ℝ,
      (∑ color, profile color) = 0 →
      (∀ color ∈ boundaryPalette (Parameters.modulus n) (boundaryHalf C n), profile color = 0) →
      ∀ record : Option (Fin (Parameters.modulus n)),
      ∀ hpos : 0 < (actualPrimaryLaw C n (beta n)).eventMass (fun color =>
        FiniteDist.boundaryRecord (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ color = record),
      (((actualPrimaryLaw C n (beta n)).condition (fun color =>
        FiniteDist.boundaryRecord (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ color = record) hpos).prod
        (actualBodyLaw C n (beta n))).expectation (fun pair =>
          pairedLift (actualPrimaryLaw C n (beta n)).weight (actualBodyLaw C n (beta n)).weight
            (fun color center => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val)
            (v7Activation C n) profile pair.1 pair.2) = 0 := by
  filter_upwards [actual_anchor_supported_eventually C hC beta hbeta,
    actual_primary_law_quarter_lower_eventually C hC beta hbeta]
    with n hs hp profile hc hb record hpos
  have hpositive (color : Fin (Parameters.modulus n)) : (actualPrimaryLaw C n (beta n)).weight color ≠ 0 := by
    have hq : (0 : ℝ) < Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
    exact ne_of_gt ((by positivity : (0 : ℝ) < 1 / (4 * (Parameters.modulus n : ℝ))).trans_le (hp color))
  apply pairedLift_boundary_mean_zero (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) _ _ _
    hpositive _ (hs profile) _ hc _ record hpos
  · intro color
    have hw : Parameters.anchorWidth n ≠ 0 := by
      unfold Parameters.anchorWidth
      exact pow_ne_zero _ (by have := Parameters.security_ge_two n; omega)
    exact (publicAnchorKernel_safe_mass _ _ 0 0 hw (Parameters.anchor_clearance n) (by norm_num)
      (by simp) color).1
  · intro color hout
    apply hb color
    simpa only [Finset.mem_compl, not_not] using hout

end
end AFT.V7Calibration

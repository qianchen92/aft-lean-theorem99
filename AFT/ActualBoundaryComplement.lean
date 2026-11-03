import AFT.ActualJointBoundary

/-! # The actual boundary complement costs only collapse followed by the inverse -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Color : Type*} [Fintype Color] [DecidableEq Color]

/-- Since the forward perturbation is an interior mass-zero profile, the
boundary collapse ignores it exactly. -/
theorem boundaryCollapse_response_eq (interior : Finset Color) (primary : Color → ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hrange : ∀ profile, operator profile - profile ∈ canonicalInteriorProfiles interior)
    (profile : Color → ℝ) :
    boundaryCollapse interior primary (operator profile) = boundaryCollapse interior primary profile := by
  have he := boundaryCollapse_eq_zero_of_canonicalInterior interior primary
    (operator profile - profile) (hrange profile)
  rw [map_sub] at he
  exact sub_eq_zero.mp he

theorem legalInputProjection_complement (interior : Finset Color) (primary : Color → ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hrange : ∀ profile, operator profile - profile ∈ canonicalInteriorProfiles interior) :
    LinearMap.id - legalInputProjection operator (boundaryIdealProjection interior primary) =
      operator.symm.toLinearMap.comp (boundaryCollapse interior primary) := by
  apply LinearMap.ext
  intro profile
  change profile - operator.symm (operator profile - boundaryCollapse interior primary (operator profile)) = _
  rw [map_sub, operator.symm_apply_apply, sub_sub_cancel, boundaryCollapse_response_eq interior primary operator hrange]
  rfl

end
end AFT

namespace AFT.GaussianSource
open V7Calibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Both actual calibrated directions differ from the identity only by
an interior mass-zero profile, without any canonicality premise on the input. -/
theorem actual_response_difference_interior_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,
      ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n →
      ∀ profile, operator profile - profile ∈ canonicalInteriorProfiles
        (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ ∧
        operator.symm profile - profile ∈ canonicalInteriorProfiles
          (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ := by
  filter_upwards [actualResponse_mass_eventually C hC, actual_physical_supports_eventually C hC,
    actual_anchor_margin_eventually C hC] with n hmass hm ha operator hop profile
  have hw : Parameters.anchorWidth n ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two n; omega)
  have hforward (input) : operator input - input ∈ canonicalInteriorProfiles
      (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ := by
    constructor
    · change (∑ color, (operator input color - input color)) = 0
      rw [Finset.sum_sub_distrib]
      have he := hmass input
      rw [← hop] at he
      simp only [LinearEquiv.coe_coe] at he
      rw [he, sub_self]
    · intro output hout
      have hb : output ∈ boundaryPalette (Parameters.modulus n) (boundaryHalf C n) := by simpa using hout
      have hbody (color : Fin (Parameters.modulus n)) :=
        (blurredAnchorKernel_safe_mass (Parameters.modulus n) (Parameters.anchorWidth n)
          (boundaryHalf C n) (fun sample => bodyShift C n sample.1)
          (pairSourceLaw C n) hw (Parameters.anchor_clearance n) hm.1.1.1
          (fun sample => by have hh := ha.1 sample; have hh' := hm.1.1.2; dsimp only; omega) color).2
          output.val (by have hh := (mem_boundaryPalette _ _ _).mp hb; omega)
      have hroot (color : Fin (Parameters.modulus n)) :=
        (blurredAnchorKernel_safe_mass (Parameters.modulus n) (Parameters.anchorWidth n)
          (boundaryHalf C n) (compensatorRootShift C n)
          (pairSourceLaw C n) hw (Parameters.anchor_clearance n) hm.1.1.1
          (fun sample => by have hh := ha.2 sample; have hh' := hm.1.1.2; omega) color).2
          output.val (by have hh := (mem_boundaryPalette _ _ _).mp hb; omega)
      have he := congrArg (fun map : Module.End ℝ (Fin (Parameters.modulus n) → ℝ) => map input output) hop
      change operator input output = actualResponse C n input output at he
      change operator input output - input output = 0
      rw [he, actualResponse_apply_formula]
      have hsign : signResponse n C (boundaryHalf C n) (startsPlus C n) (startsMinus C n)
          (pairSourceShift C n) (pairSourceLaw C n) output = 0 := by
        exact TrimmedSlice.actualSignResponse_zero_boundary _ _ _ _ _ _ _ _ _ ((mem_boundaryPalette _ _ _).mp hb)
      simp only [hsign, mul_zero, hbody, hroot, sub_self, Finset.sum_const_zero, add_zero]
  exact ⟨hforward profile, linearEquiv_inverse_difference_mem operator _ hforward profile⟩

end
end AFT.GaussianSource

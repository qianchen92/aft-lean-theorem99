import AFT.ActualBoundaryComplement
import AFT.BoundaryCollapseFibers

/-! # Fixed-order activity of the actual whole boundary projection -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color] [DecidableEq Color]

/-- Abstract the finite alphabet before specializing the growing V7 palette. -/
theorem jointLegalProjection_activity_of_inverse
    (interior : Finset Color) (primary : Color → ℝ)
    (reference : Slot → FiniteDist Color) (rates : Slot → ℝ)
    (hp : ∀ slot color, 0 < (reference slot).weight color)
    (href : ∀ slot, (reference slot).weight = primary)
    (hrates : ∀ slot, 0 < rates slot)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hrange : ∀ profile, operator profile - profile ∈ canonicalInteriorProfiles interior)
    (hinverse : ∀ slot kernel,
      activity rates reference (partialInputOperator slot operator.symm.toLinearMap
        (reference slot).weight kernel) ≤ 4 * activity rates reference kernel)
    (coordinates : List Slot) (kernel : (Slot → Color) → ℝ) :
    activity rates reference (jointLegalProjection coordinates
      (fun _ => legalInputProjection operator (boundaryIdealProjection interior primary)) reference kernel) ≤
      (1 + (8 : ℝ)^coordinates.length) * activity rates reference kernel := by
  apply jointLegalProjection_activity_le coordinates reference rates (fun slot => (hrates slot).le)
    _ 8 (by norm_num) _ kernel
  intro slot _ value
  rw [legalInputProjection_complement interior primary operator hrange,
    ← partialInputOperator_comp slot _ _ _ (fun color => (hp slot color).ne')]
  have hb := boundaryCollapse_activity_le reference rates (fun slot => (hrates slot).le) slot
    (hrates slot) interior (hp slot) value
  have hb' : activity rates reference (partialInputOperator slot (boundaryCollapse interior primary)
      (reference slot).weight value) ≤ 2 * activity rates reference value := by
    simpa only [href slot] using hb
  exact (hinverse slot _).trans
    ((mul_le_mul_of_nonneg_left hb' (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring))
end
end AFT.MixedKernel

namespace AFT.V7Calibration
open GaussianSource MixedKernel Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The complement is actual inverse after boundary collapse, with costs
four and two. Hence the whole order-k legal projection costs at most 1+8^k,
independently of lambda, alphabet size, and the selected input kernel. -/
theorem actual_joint_boundary_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop,
      ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n ∧
      ∀ (Slot : Type*) [Fintype Slot] [DecidableEq Slot], ∀ coordinates : List Slot,
      ∀ kernel : (Slot → Fin (Parameters.modulus n)) → ℝ,
      activity (fun _ : Slot => 1 / Real.sqrt (pool n : ℝ)) (fun _ : Slot => actualPrimaryLaw C n (beta n))
        (actualJointBoundaryProjection C n (beta n) coordinates operator kernel) ≤
      (1 + (8 : ℝ)^coordinates.length) * activity (fun _ : Slot => 1 / Real.sqrt (pool n : ℝ))
        (fun _ : Slot => actualPrimaryLaw C n (beta n)) kernel := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_inverse_mixed_uniform_eventually C hC beta pool htypical,
    actual_response_difference_interior_eventually C hC,
    actual_primary_law_quarter_lower_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta, htypical] with n hi hd hp hl ht
  obtain ⟨operator, hop, hinverse⟩ := hi
  refine ⟨operator, hop, ?_⟩
  intro Slot instFintype instDecidable coordinates kernel
  have hpool : 0 < pool n := by
    have hleg : 0 < Parameters.legs n := pow_pos
      (lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two n)) _
    omega
  have hpositive (color : Fin (Parameters.modulus n)) : 0 < (actualPrimaryLaw C n (beta n)).weight color := by
    have hq : (0 : ℝ) < Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
    exact (by positivity : (0 : ℝ) < 1 / (4 * (Parameters.modulus n : ℝ))).trans_le (hp color)
  have hrate : 0 < 1 / Real.sqrt (pool n : ℝ) := by positivity
  have href : (actualPrimaryLaw C n (beta n)).weight = GaussianSource.actualPrimary C (beta n) n := hl.1
  exact jointLegalProjection_activity_of_inverse
    (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
    (GaussianSource.actualPrimary C (beta n) n)
    (fun _ : Slot => actualPrimaryLaw C n (beta n))
    (fun _ : Slot => 1 / Real.sqrt (pool n : ℝ))
    (fun _ => hpositive) (fun _ => href) (fun _ => hrate) operator
    (fun profile => (hd operator hop profile).1)
    (fun slot => hinverse Slot (fun _ : Slot => actualPrimaryLaw C n (beta n))
      (fun _ : Slot => 1 / Real.sqrt (pool n : ℝ)) slot (fun _ => hrate.le) rfl rfl)
    coordinates kernel

end
end AFT.V7Calibration

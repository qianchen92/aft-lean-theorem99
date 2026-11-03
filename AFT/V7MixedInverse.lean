import AFT.MixedCoordinateOperator
import AFT.V7ActualPrimary
import AFT.V7ReferenceLaws

/-! # The actual calibrated inverse on literal joint input kernels -/

namespace AFT.V7Calibration

open Filter GaussianSource MixedKernel
open scoped BigOperators Classical Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The exact actual response inverse controls every mixed fiber of an
arbitrary joint input kernel. Other coordinates may have distinct laws and
pool rates. The threshold is uniform in those kernels and choices. -/
theorem actual_primary_inverse_mixed_uniform_eventually
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter : ℕ in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter) :
    ∀ᶠ parameter in atTop,
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = actualResponse cutoffScale parameter ∧
        ∀ (Slot : Type*) [Fintype Slot] [DecidableEq Slot],
        ∀ (reference : Slot → FiniteDist (Fin (Parameters.modulus parameter)))
          (rates : Slot → ℝ) (slot : Slot),
          (∀ index, 0 ≤ rates index) →
          reference slot = actualPrimaryLaw cutoffScale parameter (beta parameter) →
          rates slot = 1 / Real.sqrt (pool parameter : ℝ) →
          ∀ kernel : (Slot → Fin (Parameters.modulus parameter)) → ℝ,
            activity rates reference (partialInputOperator slot operator.symm.toLinearMap
              (reference slot).weight kernel) ≤ 4 * activity rates reference kernel := by
  have hbeta : ∀ᶠ parameter : ℕ in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter :=
    htypical.mono fun _ h => ⟨h.1, h.2.1⟩
  filter_upwards [actual_response_inverse_fibers_eventually cutoffScale hscale beta pool htypical,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta, htypical]
    with parameter hinverse hlaws ht
  obtain ⟨operator, hop, _, hfiber⟩ := hinverse
  refine ⟨operator, hop, ?_⟩
  intro Slot instFintype instDecidable reference rates slot hrates href hrate kernel
  have hp : 0 < pool parameter := by
    have hl : 0 < Parameters.legs parameter := pow_pos
      (lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)) _
    omega
  have hr : 0 < rates slot := by rw [hrate]; positivity
  have hprimary : (reference slot).weight = GaussianSource.actualPrimary cutoffScale (beta parameter) parameter := by
    rw [href, hlaws.1]
    rfl
  have hpartial : ∀ input : Fin (Parameters.modulus parameter) →
        ({j : Slot // j ≠ slot} → Fin (Parameters.modulus parameter)) → ℝ,
      coordinateActivity (rates slot) (reference slot).weight
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight
        (partialProfileOperator operator.symm.toLinearMap (reference slot).weight input) ≤
      2 * coordinateActivity (rates slot) (reference slot).weight
        (FiniteDist.independent (fun j : {j : Slot // j ≠ slot} => reference j)).weight input := by
    intro input
    rw [hrate, hprimary]
    exact hfiber _ _ input (FiniteDist.independent _).nonneg
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
    partialInputOperator_activity_le reference rates hrates slot hr operator.symm.toLinearMap
      2 (by norm_num) hpartial kernel

/-- Specialization of the one uniform inverse to a chosen finite coordinate type. -/
theorem actual_primary_inverse_mixed_eventually {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter : ℕ in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter) :
    ∀ᶠ parameter in atTop,
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = actualResponse cutoffScale parameter ∧
        ∀ (reference : Slot → FiniteDist (Fin (Parameters.modulus parameter)))
          (rates : Slot → ℝ) (slot : Slot),
          (∀ index, 0 ≤ rates index) →
          reference slot = actualPrimaryLaw cutoffScale parameter (beta parameter) →
          rates slot = 1 / Real.sqrt (pool parameter : ℝ) →
          ∀ kernel : (Slot → Fin (Parameters.modulus parameter)) → ℝ,
            activity rates reference (partialInputOperator slot operator.symm.toLinearMap
              (reference slot).weight kernel) ≤ 4 * activity rates reference kernel := by
  filter_upwards [actual_primary_inverse_mixed_uniform_eventually cutoffScale hscale beta pool htypical]
    with parameter h
  obtain ⟨operator, hop, hbound⟩ := h
  exact ⟨operator, hop, hbound Slot⟩

end
end AFT.V7Calibration

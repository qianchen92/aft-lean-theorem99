import AFT.PairedScoreOutput
import AFT.ActualTripleEnergy

/-! # The actual fixed-root paired output as a linear finite channel -/

namespace AFT

open scoped BigOperators Classical
noncomputable section

/-- Additivity of the literal primary/compensator score. -/
theorem pairedLift_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (primary : ι → ℝ) (body : κ → ℝ) (anchor : ι → κ → ℝ) (activation : ℝ)
    (first second : ι → ℝ) (color : ι) (center : κ) :
    pairedLift primary body anchor activation (first + second) color center =
      pairedLift primary body anchor activation first color center +
        pairedLift primary body anchor activation second color center := by
  simp only [pairedLift, applyAnchor, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]
  ring

theorem pairedLift_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (primary : ι → ℝ) (body : κ → ℝ) (anchor : ι → κ → ℝ) (activation scalar : ℝ)
    (profile : ι → ℝ) (color : ι) (center : κ) :
    pairedLift primary body anchor activation (scalar • profile) color center =
      scalar * pairedLift primary body anchor activation profile color center := by
  simp only [pairedLift, applyAnchor, Pi.smul_apply, smul_eq_mul]
  have hh : (∑ color, anchor color center * (scalar * profile color)) =
      scalar * ∑ color, anchor color center * profile color := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro color _
    ring
  rw [hh]
  ring

namespace V7Calibration

open GaussianSource BoundaryCalibration
set_option backward.isDefEq.respectTransparency false
local instance actualPairedChannelFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Four outputs in the order endpoint, endpoint, attached body,
compensator. Both roots and the actual shared-queue shift remain fixed. -/
def fixedPairedChartRaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ)
    (profile : Fin (Parameters.modulus parameter) → ℝ)
    (word : Fin 4 → Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ mark, ∑ center,
    (actualPrimaryLaw cutoffScale parameter beta).weight mark *
      (actualBodyLaw cutoffScale parameter beta).weight center *
      pairedLift (actualPrimaryLaw cutoffScale parameter beta).weight
        (actualBodyLaw cutoffScale parameter beta).weight
        (fun color position => publicAnchorKernel (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color position.val)
        (v7Activation cutoffScale parameter) profile mark center *
      publicChartRaw cutoffScale parameter mark (charts mark)
        (fun source => (actualShiftedBodyLaw cutoffScale parameter beta
          (attachedRoot + source + queue)).weight (word 2)) (word 0) (word 1) *
      (if ((word 3).val : ℤ) = (center.val : ℤ) + compensatorRoot then 1 else 0)

/-- The physical fixed-root block acts linearly on signed primary profiles.
The definition retains every original chart and center probability. -/
def actualPairedChannel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ) :
    (Fin (Parameters.modulus parameter) → ℝ) →ₗ[ℝ]
      ((Fin 4 → Fin (Parameters.modulus parameter)) → ℝ) where
  toFun := fixedPairedChartRaw cutoffScale parameter beta charts attachedRoot compensatorRoot queue
  map_add' first second := by
    funext word
    simp only [fixedPairedChartRaw, pairedLift_add, mul_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' scalar profile := by
    funext word
    simp only [fixedPairedChartRaw, pairedLift_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mark _
    apply Finset.sum_congr rfl
    intro center _
    ring

/-- Density version for the probability-weighted joint-input Hilbert tensor
bound. It multiplies by the actual primary law before applying the physical
signed-profile channel. -/
def actualPairedDensityChannel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ) :
    (Fin (Parameters.modulus parameter) → ℝ) →ₗ[ℝ]
      ((Fin 4 → Fin (Parameters.modulus parameter)) → ℝ) :=
  (actualPairedChannel cutoffScale parameter beta charts attachedRoot compensatorRoot queue).comp
    ({
      toFun := fun density color => (actualPrimaryLaw cutoffScale parameter beta).weight color * density color
      map_add' first second := by funext color; simp only [Pi.add_apply, mul_add]
      map_smul' scalar density := by
        funext color
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring } : (Fin (Parameters.modulus parameter) → ℝ) →ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ))

theorem actualPairedDensityChannel_apply (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ) (density : Fin (Parameters.modulus parameter) → ℝ)
    (word : Fin 4 → Fin (Parameters.modulus parameter)) :
    actualPairedDensityChannel cutoffScale parameter beta charts attachedRoot compensatorRoot queue density word =
      fixedPairedChartRaw cutoffScale parameter beta charts attachedRoot compensatorRoot queue
        (fun color => (actualPrimaryLaw cutoffScale parameter beta).weight color * density color) word := rfl

end V7Calibration
end
end AFT

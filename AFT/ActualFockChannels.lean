import AFT.ActualBodyFock
import AFT.ActualPairedChannel
import AFT.ChannelCentering

/-! # The literal primary and body channels into finite Fock coefficient space -/

namespace AFT.V7Calibration

open Filter GaussianSource LocalTensors
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualFockChannelsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- A canonical safe-body density is physically translated at the realized
integer shift, retaining its exact signed finite output mass. -/
def actualBodyDensityChannel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ) :
    (Fin (Parameters.modulus parameter) → ℝ) →ₗ[ℝ]
      ((Fin 1 → Fin (Parameters.modulus parameter)) → ℝ) where
  toFun density word := actualBodySignedProfile cutoffScale parameter beta density shift (word 0)
  map_add' first second := by
    funext word
    unfold actualBodySignedProfile integerShiftProfile
    simp only [Pi.add_apply, mul_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro center _
    split_ifs <;> ring
  map_smul' scalar density := by
    funext word
    unfold actualBodySignedProfile integerShiftProfile
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro center _
    split_ifs <;> ring

/-- The actual body output, including all its normalized Fock coefficients. -/
def actualBodyFockChannel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ) :
    (Fin (Parameters.modulus parameter) → ℝ) →ₗ[ℝ]
      (FockCoordinate (Fin 1) (Fin (Parameters.modulus parameter)) → ℝ) :=
  (finiteFockChannel (actualReferenceLaw cutoffScale parameter beta)
    (Parameters.dimension parameter) ((parameter : ℝ) ^ 2)).comp
      (actualBodyDensityChannel cutoffScale parameter beta shift)

/-- The actual primary paired score, all four physical outputs, and every
homogeneous Fock coefficient, with both roots and common queue still fixed. -/
def actualPrimaryFockChannel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ) :
    (Fin (Parameters.modulus parameter) → ℝ) →ₗ[ℝ]
      (FockCoordinate (Fin 4) (Fin (Parameters.modulus parameter)) → ℝ) :=
  (finiteFockChannel (actualReferenceLaw cutoffScale parameter beta)
    (Parameters.dimension parameter) ((parameter : ℝ) ^ 2)).comp
      (actualPairedDensityChannel cutoffScale parameter beta charts attachedRoot compensatorRoot queue)

/-- The fully instantiated local body channel has precisely the norm scale
`lambda^-28` needed by the arbitrary-joint-kernel tensor theorem. -/
theorem actual_body_fock_channel_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ shift : ℤ, |shift| ≤ (maxBodyShift cutoffScale parameter : ℤ) →
      ∀ input : Fin (Parameters.modulus parameter) → ℝ,
      (actualBodyLaw cutoffScale parameter (beta parameter)).expectation input = 0 →
      (∑ coordinate, actualBodyFockChannel cutoffScale parameter (beta parameter) shift input coordinate ^ 2) ≤
        (16 / (parameter : ℝ) ^ 28) ^ 2 * (actualBodyLaw cutoffScale parameter (beta parameter)).l2Sq input := by
  filter_upwards [actual_body_fock_energy_eventually cutoffScale hscale beta hbeta]
    with parameter he shift hs input hi
  change (∑ coordinate, finiteFockChannel (actualReferenceLaw cutoffScale parameter (beta parameter))
    (Parameters.dimension parameter) ((parameter : ℝ) ^ 2)
    (actualBodyDensityChannel cutoffScale parameter (beta parameter) shift input) coordinate ^ 2) ≤ _
  rw [finiteFockChannel_energy]
  exact (he input hi shift hs).trans_eq (by ring)

end
end AFT.V7Calibration

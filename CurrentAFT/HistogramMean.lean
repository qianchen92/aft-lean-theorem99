import CurrentAFT.BodyRootAverages
import CurrentAFT.BackgroundPopulationBounds
import CurrentAFT.NormalizedMeanAlgebra

/-!
# The actual complete first histogram and its fixed-queue drift

Off-body means use the genuine same-scalar pair reference. The root
average contains every free body, attachment, and queue vertex. Its only
remaining imbalance at a fixed common queue value is the queue profile
minus its true scalar average.
-/

namespace CurrentAFT.HistogramMean

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy
  ConditionalPairMean BodyRootAverages UniformBodyProfiles BackgroundCertificates
  FringeCertificate BackgroundPopulationBounds FiniteConcentration
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.bodySize Parameters.legCount
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ProposalPrimary.safeLaw

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security

private theorem pair_histogram {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist (Color × Color)) (output : Color) :
    law.expectation (fun pair => atom pair.1 output + atom pair.2 output) =
      (∑ other, law.weight (output, other)) + ∑ other, law.weight (other, output) := by
  simp only [FiniteDist.expectation, Fintype.sum_prod_type, atom, mul_add, mul_ite,
    mul_one, mul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_comm]
  simp

def offBodyMean (security : ℕ) (output : Palette security) : ℝ :=
  (scalarLaw security).expectation fun scalar => pairMean security scalar output

theorem offBodyMean_actual (security : ℕ) (output : Palette security) :
    offBodyMean security output =
      ∑ primary, (primaryLaw security).weight primary *
        endpointHistogram security (referenceLaw security primary) output := by
  have hreference (primary : Palette security) := reference_scalar_disintegration security primary
    (fun sample => atom sample.2.1 output + atom sample.2.2 output)
  simp only [pair_histogram] at hreference
  simp only [offBodyMean, FiniteDist.expectation, pairMean_actual, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro primary _
  conv_lhs =>
    arg 2
    ext scalar
    rw [mul_left_comm]
  rw [← Finset.mul_sum]
  change (primaryLaw security).weight primary *
    (scalarLaw security).expectation (fun scalar =>
      (∑ other, (pairAt security primary scalar).weight (output, other)) +
        ∑ other, (pairAt security primary scalar).weight (other, output)) = _
  rw [← hreference]
  rfl

theorem offBodyMean_leg (security : ℕ) (output : Palette security) :
    offBodyMean security output + (bodyLaw security true).weight output =
      legFirstMean security output := by
  rw [offBodyMean_actual]
  rfl

def queueLaw (security : ℕ) (queue : ℤ) : FiniteDist (Palette security) :=
  (bodyLaw security false).map (shiftEquiv security queue)

theorem queueLaw_average (security : ℕ) :
    (scalarLaw security).mix (fun scalar => queueLaw security scalar.val) = bodyLaw security true := by
  rw [← rootAverage_attachment, rootAverage_mix]
  simp_rw [rootAverage_map, rootAverage_safe]
  rfl

def rootAveragedHistogram (security : ℕ) (queue : ℤ) (output : Palette security) : ℝ :=
  freeMass security * (convolvedCenterLaw security).weight output +
    (Parameters.legCount security : ℝ) * (bodyLaw security true).weight output +
    (Parameters.modulus security : ℝ) * (queueLaw security queue).weight output +
    (Parameters.legCount security : ℝ) * offBodyMean security output

/-- Exact cancellation of every nonqueue contribution, using the actual
proposal balancing equation and the literal pair-reference mean. -/
theorem rootAveragedHistogram_centered (security : ℕ) (queue : ℤ) (output : Palette security) :
    rootAveragedHistogram security queue output -
        (Parameters.dimension security : ℝ) * uniformProfile security output =
      (Parameters.modulus security : ℝ) *
        ((queueLaw security queue).weight output - (bodyLaw security true).weight output) := by
  have hbaseline := baseline_first_histogram security output
  have hleg := offBodyMean_leg security output
  have hpopulation : freeMass security + Parameters.modulus security +
      3 * (Parameters.legCount security : ℝ) = Parameters.dimension security := by
    simp only [freeMass, Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  unfold rootAveragedHistogram
  rw [← hleg] at hbaseline
  rw [← hpopulation]
  nlinarith

def drift (security : ℕ) (queue : ℤ) : EuclideanSpace ℝ (Palette security) :=
  NormalizedMeanAlgebra.normalizationScale security •
    ProfileHilbert.whiten (uniformReference security).weight
      (fun output => rootAveragedHistogram security queue output -
        (Parameters.dimension security : ℝ) * uniformProfile security output)

theorem drift_identity (security : ℕ) (queue : ℤ) :
    drift security queue = NormalizedMeanAlgebra.normalizationScale security •
      ((Parameters.modulus security : ℝ) •
        (uniformVector security (queueLaw security queue).weight -
          uniformVector security (bodyLaw security true).weight)) := by
  simp only [drift, rootAveragedHistogram_centered]
  congr 1
  simp only [uniformVector]
  rw [← map_sub, ← map_smul]
  congr 1
  funext output
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem rootAverage_norm_le (security : ℕ) (law : FiniteDist (Palette security)) (bound : ℝ)
    (hbound : ‖uniformVector security law.weight‖ ≤ bound) :
    ‖uniformVector security (rootAverage security law).weight‖ ≤ bound := by
  apply uniformVector_mix_norm_le
  intro pair
  rw [uniformVector_map_equiv_norm]
  exact hbound

theorem queueLaw_norm_le (security : ℕ) (queue : ℤ) :
    ‖uniformVector security (queueLaw security queue).weight‖ ≤ deviation security := by
  rw [queueLaw, uniformVector_map_equiv_norm, ← rootAverage_safe]
  apply rootAverage_norm_le
  have hsafe := preRootLaw_norm_le security .queue 0
  change ‖uniformVector security ((safeLaw security).map (shiftEquiv security 0)).weight‖ ≤ deviation security at hsafe
  rw [uniformVector_map_equiv_norm] at hsafe
  exact hsafe

theorem bodyLaw_true_norm_le (security : ℕ) :
    ‖uniformVector security (bodyLaw security true).weight‖ ≤ deviation security := by
  rw [← queueLaw_average]
  exact uniformVector_mix_norm_le security (scalarLaw security) _ _
    (fun scalar => queueLaw_norm_le security scalar.val)

theorem drift_norm_le (security : ℕ) (queue : ℤ) :
    ‖drift security queue‖ ≤
      2 * (Parameters.modulus security : ℝ) * deviation security /
        Real.sqrt (Parameters.dimension security : ℝ) := by
  rw [drift_identity, NormalizedMeanAlgebra.normalizationScale, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), abs_of_nonneg (Nat.cast_nonneg _)]
  have hnorm := (norm_sub_le
    (uniformVector security (queueLaw security queue).weight)
    (uniformVector security (bodyLaw security true).weight)).trans
      (add_le_add (queueLaw_norm_le security queue) (bodyLaw_true_norm_le security))
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg (Parameters.modulus security) : (0 : ℝ) ≤ _))
    (inv_nonneg.mpr (Real.sqrt_nonneg (Parameters.dimension security : ℝ)))
  exact h.trans_eq (by ring)

end

end CurrentAFT.HistogramMean

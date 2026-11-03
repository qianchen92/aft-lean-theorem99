import AFT.V7PairResidualActivity
import AFT.ActualPairSourceDifference
import AFT.ActualPairMarginals

/-! # The finite safe pair certificate at the exact inactive source law -/

namespace AFT.V7Calibration

open GaussianSource Filter SafeConvolution
open scoped BigOperators Classical Topology

noncomputable section
attribute [local instance] actualModulusNeZero

abbrev inactivePairSample (cutoffScale : ℝ) (parameter : ℕ) :=
  (bodySample cutoffScale parameter × Bool) × Window (legCutoff cutoffScale parameter - 1)

def inactivePairSources (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (inactivePairSample cutoffScale parameter) :=
  (errorLaw (bodyBlur cutoffScale parameter)).prod (inactiveLegSource cutoffScale parameter)

def inactivePairStarts (cutoffScale : ℝ) (parameter : ℕ) (sample : inactivePairSample cutoffScale parameter) : ℤ :=
  inactiveStart cutoffScale parameter sample.1

def inactivePairShift (cutoffScale : ℝ) (parameter : ℕ) (sample : inactivePairSample cutoffScale parameter) : ℤ := sample.2

/-- The real inactive conditional source, body blur and fair anchor coin
are retained together, with no additional inverse event probability. -/
theorem averagedInactivePair_mixture (cutoffScale : ℝ) (parameter : ℕ) :
    averagedInactivePair cutoffScale parameter =
      TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
        (inactivePairStarts cutoffScale parameter) (inactivePairShift cutoffScale parameter)
        (inactivePairSources cutoffScale parameter).weight (Parameters.anchorWidth parameter) := by
  funext first second
  simp only [averagedInactivePair, inactivePairAtSource_mixture, TrimmedSlice.mixedPair,
    inactivePairSources, Fintype.sum_prod_type, FiniteDist.prod_weight, inactivePairStarts, inactivePairShift,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coin _
  apply Finset.sum_congr rfl
  intro source _
  ring

theorem inactivePairSources_physical_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter in atTop,
      (0 ≤ boundaryHalf cutoffScale parameter ∧ boundaryHalf cutoffScale parameter ≤ Parameters.safeMargin parameter) ∧
      (∀ sample shift, shift ∈ anchorInterval (inactivePairStarts cutoffScale parameter sample) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
      (∀ sample, |inactivePairShift cutoffScale parameter sample| ≤ legCutoff cutoffScale parameter) := by
  filter_upwards [actual_physical_supports_eventually cutoffScale hscale] with parameter hs
  refine ⟨hs.1.1, ?_, ?_⟩
  · intro sample shift hh
    rcases sample with ⟨⟨body, coin⟩, source⟩
    cases coin with
    | false => exact hs.1.2.2.1 (body, source) shift hh
    | true => exact hs.1.2.1 (body, source) shift hh
  · intro sample
    exact (abs_le.mpr (Finset.mem_Icc.mp sample.2.property)).trans
      (by exact_mod_cast Nat.sub_le (legCutoff cutoffScale parameter) 1)

/-- The actual inactive pair, rather than an arbitrary admissible pair,
has a literal complete mixed residual certificate at the stated power. -/
theorem actual_inactive_pair_residual_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2 * pool parameter) :
    ∀ᶠ parameter in atTop, ∀ (body : FiniteDist (Fin (Parameters.modulus parameter))) (bodyPool radius : ℝ),
      RepresentedPolynomial.inputWeight (actualPrimaryLaw cutoffScale parameter (beta parameter)) body
        (pool parameter : ℝ) bodyPool radius
        (actualPairResidualInput cutoffScale parameter (beta parameter) (averagedInactivePair cutoffScale parameter)) ≤
      (Real.sqrt (pool parameter : ℝ))⁻¹ ^ 2 * pairResidualMixedConstant cutoffScale / (parameter : ℝ) ^ 2 := by
  have hh := actual_pair_residual_activity_eventually cutoffScale hscale beta pool htypical
    (boundaryHalf cutoffScale) (inactivePairStarts cutoffScale) (inactivePairShift cutoffScale)
    (inactivePairSources cutoffScale) (inactivePairSources_physical_eventually cutoffScale hscale)
  simpa only [averagedInactivePair_mixture] using hh

end
end AFT.V7Calibration

import AFT.PairDifferenceReference
import AFT.ActualTriples

/-! # Actual inactive-pair source differences, with the real fair anchor law -/

namespace AFT.V7Calibration

open GaussianSource Filter
open scoped BigOperators Classical Topology

noncomputable section

def inactiveStart (cutoffScale : ℝ) (parameter : ℕ) : bodySample cutoffScale parameter × Bool → ℤ :=
  fun sample => if sample.2 then (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample.1
    else -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample.1

theorem inactivePairAtSource_mixture (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) :
    inactivePairAtSource cutoffScale parameter source first second =
      TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
        (inactiveStart cutoffScale parameter) (fun _ => source) (errorLaw (bodyBlur cutoffScale parameter)).weight
        (Parameters.anchorWidth parameter) first second := by
  simp only [inactivePairAtSource, TrimmedSlice.mixedPair, errorLaw, Fintype.sum_prod_type,
    FiniteDist.prod_weight, FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat, inactiveStart,
    Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm]
  ring_nf
  simp only [Finset.sum_mul]

/-- These are uniform bounds for the actual inactive pair, for any two
allowed source values. Averaging the original body/sign randomness does
not pay a conditioning-probability denominator. -/
theorem actual_inactive_pair_source_bounds_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ firstSource secondSource : ℤ,
      |firstSource| ≤ legCutoff cutoffScale parameter → |secondSource| ≤ legCutoff cutoffScale parameter →
      ∀ first : Fin (Parameters.modulus parameter),
      (∑ second, (inactivePairAtSource cutoffScale parameter firstSource first second -
        inactivePairAtSource cutoffScale parameter secondSource first second) ^ 2) ≤
        8 * ((secondSource - firstSource).natAbs : ℝ) /
          ((Parameters.modulus parameter : ℝ) ^ 2 * (Parameters.anchorWidth parameter : ℝ) ^ 2) ∧
      (∑ second, |inactivePairAtSource cutoffScale parameter firstSource first second -
        inactivePairAtSource cutoffScale parameter secondSource first second|) ≤
        4 * ((secondSource - firstSource).natAbs : ℝ) /
          ((Parameters.modulus parameter : ℝ) * (Parameters.anchorWidth parameter : ℝ)) := by
  have hphysical := actual_physical_supports_eventually cutoffScale hscale
  have hclear := v7_primaryCalibration_clearance_eventually cutoffScale hscale (boundaryHalf cutoffScale)
    (hphysical.mono fun _ h => h.1.1)
  filter_upwards [hphysical, hclear] with parameter hs hc
  intro firstSource secondSource hfirst hsecond first
  have hq : 0 < (Parameters.modulus parameter : ℝ) := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hstarts : ∀ sample shift, shift ∈ anchorInterval (inactiveStart cutoffScale parameter sample) (Parameters.anchorWidth parameter) →
      |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ) := by
    intro sample shift hh
    rcases sample with ⟨sample, coin⟩
    cases coin with
    | false => exact hs.1.2.2.1 (sample, windowZero _) shift hh
    | true => exact hs.1.2.1 (sample, windowZero _) shift hh
  have hD : (Parameters.modulus parameter : ℝ) / 2 ≤ (Parameters.modulus parameter : ℝ) -
      2 * boundaryHalf cutoffScale parameter - 3 * (Parameters.anchorWidth parameter : ℤ) - legCutoff cutoffScale parameter := by
    have hh : 2 * (3 * (Parameters.anchorWidth parameter : ℝ) + 2 * boundaryHalf cutoffScale parameter + legCutoff cutoffScale parameter) ≤
        Parameters.modulus parameter := by exact_mod_cast hc.2
    push_cast
    linarith
  have hsq := TrimmedSlice.mixedPair_source_fiber_square_le (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    firstSource secondSource (3 * Parameters.anchorWidth parameter) (legCutoff cutoffScale parameter)
    (inactiveStart cutoffScale parameter) (errorLaw (bodyBlur cutoffScale parameter)) (Parameters.anchorWidth parameter)
    ((Parameters.modulus parameter : ℝ) / 2) (by positivity) hstarts hfirst hsecond (by simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hD) first
  have hl1 := TrimmedSlice.mixedPair_source_fiber_l1_le (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    firstSource secondSource (3 * Parameters.anchorWidth parameter) (legCutoff cutoffScale parameter)
    (inactiveStart cutoffScale parameter) (errorLaw (bodyBlur cutoffScale parameter)) (Parameters.anchorWidth parameter)
    ((Parameters.modulus parameter : ℝ) / 2) (by positivity) hstarts hfirst hsecond (by simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hD) first
  simp only [inactivePairAtSource_mixture]
  constructor
  · exact hsq.trans_eq (by ring)
  · exact hl1.trans_eq (by ring)

end
end AFT.V7Calibration

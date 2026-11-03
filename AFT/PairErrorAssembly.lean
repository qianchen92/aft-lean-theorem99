import AFT.CoreCenteringDifference
import AFT.CanonicalSmoothing
import AFT.V7SafePairInput

/-! # Complete error of the actual finite safe pair input -/

namespace AFT.SafePair

open scoped BigOperators
open SafeConvolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coreSeed_reference_error_le (core : Finset ι) (hne : core.Nonempty)
    (mass : ι → ι → ℝ) (upper : ℝ) (hu : 0 ≤ upper)
    (hmass : ∀ first second, 0 ≤ mass first second)
    (htotal : (∑ first, ∑ second, mass first second) ≤ 1)
    (hrow : ∀ first, (∑ second, mass first second) ≤ upper)
    (hcolumn : ∀ second, (∑ first, mass first second) ≤ upper) :
    pairCountingL2 (coreSeed core mass - canonicalPair (fun _ => 1 / (Fintype.card ι : ℝ))
      (restrictPair core mass)) ≤
      Real.sqrt (1 / (core.card : ℝ) - 1 / (Fintype.card ι : ℝ)) *
        (2 * Real.sqrt upper + Real.sqrt (1 / (core.card : ℝ)) +
          Real.sqrt (1 / (Fintype.card ι : ℝ))) := by
  have hnonneg (first second : ι) : 0 ≤ restrictPair core mass first second := by
    unfold restrictPair; split_ifs
    · exact hmass first second
    · exact le_rfl
  have hle (first second : ι) : restrictPair core mass first second ≤ mass first second := by
    unfold restrictPair; split_ifs <;> simp_all
  have hh := canonicalPair_reference_L2_le (uniformFiniteProfile core)
    (fun _ => 1 / (Fintype.card ι : ℝ)) (restrictPair core mass) upper hu hnonneg
    ((Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hle x y).trans htotal)
    (fun x => (Finset.sum_le_sum fun y _ => hle x y).trans (hrow x))
    (fun y => (Finset.sum_le_sum fun x _ => hle x y).trans (hcolumn y))
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    have hp := (Finset.card_pos.mpr hne).trans_le (Finset.card_le_univ core)
    positivity
  have hfull : countingL2 (fun _ : ι => 1 / (Fintype.card ι : ℝ)) =
      Real.sqrt (1 / (Fintype.card ι : ℝ)) := by
    unfold countingL2
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hcore : countingL2 (uniformFiniteProfile core) = Real.sqrt (1 / (core.card : ℝ)) := by
    unfold countingL2
    rw [uniformFiniteProfile_square core hne]
  have hdiff : countingL2 (uniformFiniteProfile core - fun _ : ι => 1 / (Fintype.card ι : ℝ)) =
      Real.sqrt (1 / (core.card : ℝ) - 1 / (Fintype.card ι : ℝ)) := by
    unfold countingL2
    simp only [Pi.sub_apply, uniformCore_difference_square core hne]
  simpa only [coreSeed, hcore, hfull, hdiff] using hh

end AFT.SafePair

namespace AFT.GaussianSource

open scoped BigOperators Classical
open SafeConvolution

attribute [local instance] actualModulusNeZero

/-- The complete residual contains the Neumann remainder, the change of
core reference, the actual integer-pair smoothing, and both deleted edges.
No term of the finite input or the target pair is truncated. -/
theorem actualPairInput_error_le (parameter depth : ℕ) (hp : 0 < parameter)
    (mass : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ) :
    let core := pairCore parameter depth
    let original := fun color : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) => mass color.1 color.2
    let restricted := fun color : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) => SafePair.restrictPair core mass color.1 color.2
    let seed := actualPairCoreSeed parameter depth mass
    countingL2 (convolution (actualRootPair parameter).weight
        (actualCompactRootInput parameter depth seed) - uniformCanonical original) ≤
      (12 / (parameter : ℝ)) ^ (depth + 1) * countingL2 seed +
      countingL2 (seed - uniformCanonical restricted) +
      (depth + 1 : ℕ) * countingL2 (convolution (actualCompactBox parameter).weight restricted - restricted) +
      countingL2 (restricted - original) := by
  dsimp only
  let original := fun color : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) => mass color.1 color.2
  let seed := actualPairCoreSeed parameter depth mass
  let image := convolution (actualRootPair parameter).weight (actualCompactRootInput parameter depth seed)
  let smooth := (convolution (actualCompactBox parameter).weight ^ (depth + 1)) seed
  have heq : image - uniformCanonical original = (image - smooth) + (smooth - uniformCanonical original) := by abel
  change countingL2 (image - uniformCanonical original) ≤ _
  rw [heq]
  have hs := smoothed_core_error_L2_le (actualCompactBox parameter) (pairCore parameter depth) mass (depth + 1)
  have hr := actualCompactRootInput_residual_L2_le parameter depth hp seed
  exact (countingL2_add _ _).trans (by
    simpa only [seed, actualPairCoreSeed, add_assoc] using add_le_add hr hs)

end AFT.GaussianSource

import AFT.MarkedSafePair

/-! # The actual inactive source and shared-source local triple identities -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

namespace FiniteDist
variable {α : Type*} [Fintype α]

theorem atom_le_one (p : FiniteDist α) (point : α) : p.weight point ≤ 1 := by
  have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => p.nonneg i) (Finset.mem_univ point)
  simpa only [p.sum_one] using hh

/-- Remove an actual atom of marked mass, and normalize the inactive branch. -/
def removeAtom (p : FiniteDist α) (point : α) (mark : ℝ)
    (hmark : mark ≤ p.weight point) (hsmall : mark < 1) : FiniteDist α where
  weight sample := (p.weight sample - if sample = point then mark else 0) / (1 - mark)
  nonneg sample := by
    apply div_nonneg _ (by linarith)
    split_ifs with heq
    · subst sample; exact sub_nonneg.mpr hmark
    · simpa using p.nonneg sample
  sum_one := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, p.sum_one]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact div_self (by linarith)

theorem removeAtom_weight_identity (p : FiniteDist α) (point : α) (mark : ℝ)
    (hmark : mark ≤ p.weight point) (hsmall : mark < 1) (sample : α) :
    (1 - mark) * (p.removeAtom point mark hmark hsmall).weight sample +
      (if sample = point then mark else 0) = p.weight sample := by
  dsimp only [removeAtom]
  field_simp [show 1 - mark ≠ 0 by linarith]
  ring

end FiniteDist

namespace GaussianSource

theorem activation_le_second_atom (firstWidth secondWidth : ℝ) (cutoff featureCount : ℕ) :
    activation firstWidth secondWidth cutoff featureCount ≤ (windowGaussian secondWidth cutoff).weight (windowZero cutoff) := by
  by_cases hf : featureCount = 0
  · simp only [activation, hf, Nat.cast_zero, mul_zero, div_zero, zero_mul]
    exact (windowGaussian secondWidth cutoff).nonneg _
  · have hf' : (1 : ℝ) ≤ featureCount := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf
    have hmark : 1 / (100 * (featureCount : ℝ)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith
    unfold activation
    rw [FiniteDist.prod_weight]
    have hfirst := (windowGaussian firstWidth cutoff).atom_le_one (windowZero cutoff)
    have hsecond := (windowGaussian secondWidth cutoff).nonneg (windowZero cutoff)
    have hh := mul_le_mul hmark hfirst ((windowGaussian firstWidth cutoff).nonneg _) (by norm_num)
    simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hh hsecond

/-- Exactly the conditional second-source law of the inactive branch.
The removed mass is the full true activation probability. -/
def inactiveLegSource (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (Window (legCutoff cutoffScale parameter - 1)) :=
  (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).removeAtom
    (windowZero (legCutoff cutoffScale parameter - 1)) (v7Activation cutoffScale parameter)
    (activation_le_second_atom _ _ _ _) ((activation_le_one_hundredth _ _ _ _).trans_lt (by norm_num))

theorem inactiveLegSource_weight (cutoffScale : ℝ) (parameter : ℕ) (sample : Window (legCutoff cutoffScale parameter - 1)) :
    (inactiveLegSource cutoffScale parameter).weight sample =
      ((windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight sample -
        if sample = windowZero (legCutoff cutoffScale parameter - 1) then v7Activation cutoffScale parameter else 0) /
          (1 - v7Activation cutoffScale parameter) := by
  by_cases h : sample = windowZero (legCutoff cutoffScale parameter - 1) <;>
    simp [inactiveLegSource, FiniteDist.removeAtom, h]

theorem inactiveLegSource_mixture (cutoffScale : ℝ) (parameter : ℕ) (sample : Window (legCutoff cutoffScale parameter - 1)) :
    (1 - v7Activation cutoffScale parameter) * (inactiveLegSource cutoffScale parameter).weight sample +
      (if sample = windowZero (legCutoff cutoffScale parameter - 1) then v7Activation cutoffScale parameter else 0) =
        (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight sample :=
  by
    rw [inactiveLegSource_weight]
    have hsmall : v7Activation cutoffScale parameter < 1 := (activation_le_one_hundredth _ _ _ _).trans_lt (by norm_num)
    field_simp [show 1 - v7Activation cutoffScale parameter ≠ 0 by linarith]
    ring

end GaussianSource

namespace V7Calibration
open GaussianSource

/-- A literal integer translation, retaining the palette boundary. -/
def integerShiftProfile (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (shift : ℤ) (output : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ center, if (output.val : ℤ) = (center.val : ℤ) + shift then profile center else 0

/-- The two physical ordered endpoint windows at one fixed attachment source. -/
def inactivePairAtSource (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  (TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (fun sample => (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample)
    (fun _ => source) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) first second +
   TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (fun sample => -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample)
    (fun _ => source) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) first second) / 2

/-- The same local source shifts the attached body, after its actual root marginal. -/
def attachedBodyAtSource (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue source : ℤ)
    (output : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ root : Window (v7RootCutoff parameter),
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter)).weight root *
      integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) ((root : ℤ) + source + queue) output

/-- The marked endpoint law uses the true primary and the full public companion blur. -/
def actualMarkedPair (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  actualPrimary cutoffScale parameter beta first *
    blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) first second.val

def averagedInactivePair (cutoffScale : ℝ) (parameter : ℕ) (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ source, (inactiveLegSource cutoffScale parameter).weight source * inactivePairAtSource cutoffScale parameter source first second

def averagedInactiveBody (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (output : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ source, (inactiveLegSource cutoffScale parameter).weight source * attachedBodyAtSource cutoffScale parameter beta queue source output

/-- The exact covariance from the shared inactive attachment source. -/
def actualInactiveResidual (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (first second attached : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
    (inactivePairAtSource cutoffScale parameter source first second - averagedInactivePair cutoffScale parameter first second) *
    (attachedBodyAtSource cutoffScale parameter beta queue source attached - averagedInactiveBody cutoffScale parameter beta queue attached)

/-- The physical local triple keeps the common source in its two factors,
including the zero-source active branch with its unconditional probability. -/
def actualLocalTriple (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (first second attached : Fin (Parameters.modulus parameter)) : ℝ :=
  (1 - v7Activation cutoffScale parameter) *
    (∑ source, (inactiveLegSource cutoffScale parameter).weight source *
      inactivePairAtSource cutoffScale parameter source first second * attachedBodyAtSource cutoffScale parameter beta queue source attached) +
    v7Activation cutoffScale parameter * actualMarkedPair cutoffScale parameter beta first second *
      attachedBodyAtSource cutoffScale parameter beta queue 0 attached

def localPairMixture (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  (1 - v7Activation cutoffScale parameter) * averagedInactivePair cutoffScale parameter first second +
    v7Activation cutoffScale parameter * actualMarkedPair cutoffScale parameter beta first second

def localBodyMixture (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (attached : Fin (Parameters.modulus parameter)) : ℝ :=
  (1 - v7Activation cutoffScale parameter) * averagedInactiveBody cutoffScale parameter beta queue attached +
    v7Activation cutoffScale parameter * attachedBodyAtSource cutoffScale parameter beta queue 0 attached

/-- Exact inactive covariance identity for the actual source law. -/
theorem actual_inactive_covariance (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (first second attached : Fin (Parameters.modulus parameter)) :
    (∑ source, (inactiveLegSource cutoffScale parameter).weight source *
      inactivePairAtSource cutoffScale parameter source first second * attachedBodyAtSource cutoffScale parameter beta queue source attached) =
      averagedInactivePair cutoffScale parameter first second * averagedInactiveBody cutoffScale parameter beta queue attached +
        actualInactiveResidual cutoffScale parameter beta queue first second attached := by
  let P := averagedInactivePair cutoffScale parameter first second
  let B := averagedInactiveBody cutoffScale parameter beta queue attached
  have hpoint (source : Window (legCutoff cutoffScale parameter - 1)) :
      (inactiveLegSource cutoffScale parameter).weight source *
        (inactivePairAtSource cutoffScale parameter source first second - P) *
        (attachedBodyAtSource cutoffScale parameter beta queue source attached - B) =
      (inactiveLegSource cutoffScale parameter).weight source * inactivePairAtSource cutoffScale parameter source first second *
        attachedBodyAtSource cutoffScale parameter beta queue source attached -
      ((inactiveLegSource cutoffScale parameter).weight source * inactivePairAtSource cutoffScale parameter source first second) * B -
      P * ((inactiveLegSource cutoffScale parameter).weight source * attachedBodyAtSource cutoffScale parameter beta queue source attached) +
      (inactiveLegSource cutoffScale parameter).weight source * (P * B) := by ring
  change _ = P * B + ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
    (inactivePairAtSource cutoffScale parameter source first second - P) *
    (attachedBodyAtSource cutoffScale parameter beta queue source attached - B)
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    (inactiveLegSource cutoffScale parameter).sum_one, one_mul]
  change _ = P * B + (_ - P * B - P * B + P * B)
  ring

/-- The exact decomposition from Section 9, with no independent-source
replacement and with the full active covariance retained. -/
theorem actual_local_triple_decomposition (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (first second attached : Fin (Parameters.modulus parameter)) :
    actualLocalTriple cutoffScale parameter beta queue first second attached =
      localPairMixture cutoffScale parameter beta first second * localBodyMixture cutoffScale parameter beta queue attached +
      (1 - v7Activation cutoffScale parameter) * actualInactiveResidual cutoffScale parameter beta queue first second attached +
      v7Activation cutoffScale parameter * (1 - v7Activation cutoffScale parameter) *
        (actualMarkedPair cutoffScale parameter beta first second - averagedInactivePair cutoffScale parameter first second) *
        (attachedBodyAtSource cutoffScale parameter beta queue 0 attached - averagedInactiveBody cutoffScale parameter beta queue attached) := by
  unfold actualLocalTriple localPairMixture localBodyMixture
  rw [actual_inactive_covariance]
  ring

end V7Calibration
end
end AFT

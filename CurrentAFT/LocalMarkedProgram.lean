import CurrentAFT.LocalDiffuseProgram
import CurrentAFT.ActualPublicLegDisintegration

/-!
# Rational entries of the actual marked pair channel

The two public blur edges are approximated by the current Gaussian window
program.  The fair direction coin and uniform anchor index are averaged
exactly.  The retained protected scalar is an input throughout.
-/

namespace CurrentAFT.LocalMarkedProgram

open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy ActualPublicLegCharge
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def companionValue (colors width primary : ℕ) (source blur : ℤ) (coin : Bool) (index : Fin width) : ℤ :=
  (colors : ℤ) - 1 - primary +
    (if LocalDiffuseProgram.direction colors primary coin then
      (width : ℤ) + index.val else -((width : ℤ) + index.val)) + blur - source

def pointEntry (colors width primary : ℕ) (source blur : ℤ) (coin : Bool)
    (index : Fin width) (first second : ℕ) : ℚ :=
  if primary = first ∧ (companionValue colors width primary source blur coin index).toNat = second then 1 else 0

def coinEntry (colors width primary : ℕ) (source blur : ℤ) (coin : Bool) (first second : ℕ) : ℚ :=
  (width : ℚ)⁻¹ * ∑ index : Fin width, pointEntry colors width primary source blur coin index first second

def blurEntry (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) : ℚ :=
  (coinEntry colors width primary source blur true first second +
    coinEntry colors width primary source blur false first second) / 2

def evaluate (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  ∑ left : Window cutoff, ∑ right : Window cutoff,
    windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits left *
      windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits right *
        blurEntry colors width primary source first second (left.val - right.val)

def current (security bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  evaluate security (PublicParameterProgram.modulus security).count ((security + 2)^48)
    (((security + 2)^2 - 1) / 2) bits primary source first second

noncomputable section
open scoped Classical
local instance markedIndexNonempty (security : ℕ) : Nonempty (InwardAnchor.Index security) :=
  ⟨⟨0, InwardAnchor.anchorWidth_pos security⟩⟩
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff

theorem pointEntry_bound (colors width primary : ℕ) (source blur : ℤ) (coin : Bool)
    (index : Fin width) (first second : ℕ) :
    |(pointEntry colors width primary source blur coin index first second : ℝ)| ≤ 1 := by
  unfold pointEntry
  split_ifs <;> norm_num

theorem coinEntry_bound (colors width primary : ℕ) (source blur : ℤ) (coin : Bool) (first second : ℕ) :
    |(coinEntry colors width primary source blur coin first second : ℝ)| ≤ 1 := by
  by_cases hw : width = 0
  · simp [coinEntry, hw]
  have hwR : (width : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hw
  have hsum : |∑ index : Fin width, (pointEntry colors width primary source blur coin index first second : ℝ)| ≤ width := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _index : Fin width, (1 : ℝ) := Finset.sum_le_sum (fun index _ => pointEntry_bound _ _ _ _ _ _ index _ _)
      _ = _ := by simp
  simp only [coinEntry, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum, abs_mul,
    abs_inv, abs_of_nonneg (Nat.cast_nonneg width : (0 : ℝ) ≤ width)]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq
    (inv_mul_cancel₀ hwR)

theorem blurEntry_bound (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) :
    |(blurEntry colors width primary source first second blur : ℝ)| ≤ 1 := by
  have ht := coinEntry_bound colors width primary source blur true first second
  have hf := coinEntry_bound colors width primary source blur false first second
  unfold blurEntry
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  linarith only [ht, hf]

theorem pointEntry_cast (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (blur : BlurSeed security) (coin : Bool)
    (index : InwardAnchor.Index security) :
    (pointEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
      (blur.1.val - blur.2.val) coin index first.val second.val : ℝ) =
      (markedLaw security primary source ⟨true, coin, index, blur⟩).weight (first, second) := by
  rw [markedLaw_weight]
  have hvalue : companionValue (Parameters.modulus security) (Parameters.anchorWidth security)
      primary.val source.val (blur.1.val - blur.2.val) coin index =
      (Parameters.modulus security : ℤ) - 1 - primary.val +
        publicShift security primary ⟨true, coin, index, blur⟩ - source.val := by
    unfold companionValue publicShift signedOffset InwardAnchor.offset
    change (Parameters.modulus security : ℤ) - 1 - primary.val +
      (if InwardAnchor.positiveDirection security primary coin then
        (Parameters.anchorWidth security : ℤ) + index.val else -((Parameters.anchorWidth security : ℤ) + index.val)) +
      (blur.1.val - blur.2.val) - source.val = _
    ring
  have hpoint : (companionValue (Parameters.modulus security) (Parameters.anchorWidth security)
      primary.val source.val (blur.1.val - blur.2.val) coin index).toNat =
      (markedPoint security primary source ⟨true, coin, index, blur⟩).val := by
    rw [markedPoint_value, hvalue]
  simp only [pointEntry, hpoint, Prod.mk.injEq, Fin.ext_iff]
  split_ifs <;> norm_num

theorem coinEntry_cast (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (blur : BlurSeed security) (coin : Bool) :
    (coinEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
      (blur.1.val - blur.2.val) coin first.val second.val : ℝ) =
      (FiniteDist.uniform (InwardAnchor.Index security)).expectation (fun index =>
        (markedLaw security primary source ⟨true, coin, index, blur⟩).weight (first, second)) := by
  simp only [coinEntry, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum,
    pointEntry_cast, FiniteDist.expectation, FiniteDist.uniform_weight, Fintype.card_fin,
    Finset.mul_sum]

theorem evaluate_cast (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ) :
    (evaluate security colors width cutoff bits primary source first second : ℝ) =
      ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits).prod
        (windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits)).expectation
          (fun blur => (blurEntry colors width primary source first second (blur.1.val - blur.2.val) : ℝ)) := by
  simp only [evaluate, Rat.cast_sum, Rat.cast_mul, FiniteDist.expectation,
    FiniteDist.prod_weight, Fintype.sum_prod_type, windowApproxLaw]

theorem ideal_formula (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    (publicBlurLaw security).expectation (fun blur =>
      (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
        first.val second.val (blur.1.val - blur.2.val) : ℝ)) =
      (markedPairAt security primary source).weight (first, second) := by
  rw [← marked_average]
  change _ = (FiniteDist.uniform Bool).expectation (fun coin =>
    (FiniteDist.uniform (InwardAnchor.Index security)).expectation (fun index =>
      (publicBlurLaw security).expectation (fun blur =>
        (markedLaw security primary source ⟨true, coin, index, blur⟩).weight (first, second))))
  simp_rw [FiniteDist.expectation_comm (FiniteDist.uniform (InwardAnchor.Index security)) (publicBlurLaw security)]
  rw [FiniteDist.expectation_comm (FiniteDist.uniform Bool) (publicBlurLaw security)]
  apply congrArg (FiniteDist.expectation (publicBlurLaw security))
  funext blur
  simp only [blurEntry, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, coinEntry_cast,
    FiniteDist.expectation, Fintype.sum_bool, FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat]
  ring

theorem evaluate_error (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(evaluate security (Parameters.modulus security) (Parameters.anchorWidth security) (edgeCutoff security)
      bits primary.val source.val first.val second.val : ℝ) -
        (markedPairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits
  have hscalar : (∑ point, |approximate.weight point - (edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits :=
    windowApproxLaw_l1 _ _ _ _ (WindowGaussianSampler.squaredWidth_positive security)
      (WindowGaussianSampler.squaredWidth_real security).symm
  have hprod := FiniteDist.l1_prod_le approximate (edgeLaw security) approximate (edgeLaw security)
  have hl1 : (∑ blur, |(approximate.prod approximate).weight blur - (publicBlurLaw security).weight blur|) ≤
      2 / (2 : ℝ)^bits := hprod.trans ((add_le_add hscalar hscalar).trans_eq (by ring))
  calc
    _ = |(approximate.prod approximate).expectation (fun blur =>
        (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
          first.val second.val (blur.1.val - blur.2.val) : ℝ)) -
      (publicBlurLaw security).expectation (fun blur =>
        (blurEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
          first.val second.val (blur.1.val - blur.2.val) : ℝ))| :=
        congrArg abs (congrArg₂ (· - ·) (evaluate_cast _ _ _ _ _ _ _ _ _)
          (ideal_formula security primary first second source).symm)
    _ ≤ _ := (CyclePatternProgram.expectation_difference_le_l1 _ _ _ 1
      (fun blur => blurEntry_bound _ _ _ _ _ _ _)).trans (by simpa only [one_mul] using hl1)

theorem current_error (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(current security bits primary.val source.val first.val second.val : ℝ) -
      (markedPairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  have hwidth : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [DiffuseProfiles.anchorWidth_eq, Parameters.base]
  have hcutoff : ((security + 2)^2 - 1) / 2 = edgeCutoff security := by
    simp only [edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  unfold current
  rw [PublicParameterProgram.modulus_value, hwidth, hcutoff]
  exact evaluate_error security bits primary first second source

end
end CurrentAFT.LocalMarkedProgram

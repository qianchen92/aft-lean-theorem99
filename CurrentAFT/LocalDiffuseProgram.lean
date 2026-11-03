import CurrentAFT.CyclePatternProgram
import CurrentAFT.PublicParameterProgram
import CurrentAFT.LocalReferenceEnergy
import AFT.ActualConditionalPairProgram

/-! # A current conditional diffuse-pair entry program

The protected scalar is retained as an input throughout. Only the two
independent public blur edges are rationally approximated. This program
uses the actual integer trimmed-slice formula, including its varying
denominator, rather than a circular uniform replacement.
-/
namespace CurrentAFT.LocalDiffuseProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def direction (colors primary : ℕ) (coin : Bool) : Bool :=
  if 2 * primary < colors - 1 then false else if colors - 1 < 2 * primary then true else coin

def coinEntry (colors width primary : ℕ) (source blur : ℤ) (coin : Bool) (first second : ℕ) : ℚ :=
  AFT.V7Calibration.averagedPairProgram colors 1
    ((if direction colors primary coin then (width : ℤ) else -2 * (width : ℤ) + 1) + blur)
    source width first second

def blurEntry (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) : ℚ :=
  (coinEntry colors width primary source blur true first second +
    coinEntry colors width primary source blur false first second) / 2

def evaluate (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  ∑ left : Window cutoff, ∑ right : Window cutoff,
    windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits left *
      windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits right *
        blurEntry colors width primary source first second (left.val - right.val)

/-- All public parameters used by the evaluator are computed. The later
bit-work accounting for this entry evaluator is a separate obligation. -/
def current (security bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  evaluate security (PublicParameterProgram.modulus security).count ((security + 2)^48)
    (((security + 2)^2 - 1) / 2) bits primary source first second

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw

theorem coinEntry_cast (security : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (blur : BlurSeed security) (coin : Bool) :
    (coinEntry (Parameters.modulus security) (Parameters.anchorWidth security) primary.val source.val
      (blur.1.val - blur.2.val) coin first.val second.val : ℝ) =
      (FirstHistogram.diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) (blur, source)).weight
        (first, second) := by
  rw [FirstHistogram.diffuseSeedPair_weight]
  unfold coinEntry
  rw [AFT.V7Calibration.averagedPairProgram_cast]
  rfl

theorem blurEntry_bound (colors width primary : ℕ) (source : ℤ) (first second : ℕ) (blur : ℤ) :
    |(blurEntry colors width primary source first second blur : ℝ)| ≤ 1 := by
  have htrue := AFT.V7Calibration.averagedPairProgram_abs_le_one colors 1
    ((if direction colors primary true then (width : ℤ) else -2 * (width : ℤ) + 1) + blur) source width first second
  have hfalse := AFT.V7Calibration.averagedPairProgram_abs_le_one colors 1
    ((if direction colors primary false then (width : ℤ) else -2 * (width : ℤ) + 1) + blur) source width first second
  unfold blurEntry
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  change (|(coinEntry colors width primary source blur true first second : ℝ)| +
    |(coinEntry colors width primary source blur false first second : ℝ)|) / 2 ≤ 1
  change |(coinEntry colors width primary source blur true first second : ℝ)| ≤ 1 at htrue
  change |(coinEntry colors width primary source blur false first second : ℝ)| ≤ 1 at hfalse
  linarith only [htrue, hfalse]

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
      (diffusePairAt security primary source).weight (first, second) := by
  unfold diffusePairAt
  change _ = (FiniteDist.uniform Bool).expectation (fun coin => (publicBlurLaw security).expectation
    (fun blur => (FirstHistogram.diffuseSeedPair security
      (InwardAnchor.positiveDirection security primary coin) (blur, source)).weight (first, second)))
  conv_rhs => rw [FiniteDist.expectation_comm]
  apply congrArg (FiniteDist.expectation _)
  funext blur
  simp only [blurEntry, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, coinEntry_cast,
    FiniteDist.expectation, Fintype.sum_bool, FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat]
  ring

/-- A simultaneous entrywise estimate, for all public controls, endpoints,
and the retained protected scalar. No final response error is assumed. -/
theorem evaluate_error (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(evaluate security (Parameters.modulus security) (Parameters.anchorWidth security) (edgeCutoff security)
      bits primary.val source.val first.val second.val : ℝ) -
        (diffusePairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits
  have hscalar : (∑ point, |approximate.weight point - (edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits :=
    windowApproxLaw_l1 _ _ _ _ (WindowGaussianSampler.squaredWidth_positive security)
      (WindowGaussianSampler.squaredWidth_real security).symm
  have hprod := FiniteDist.l1_prod_le approximate (edgeLaw security) approximate (edgeLaw security)
  have hl1 : (∑ blur, |(approximate.prod approximate).weight blur - (publicBlurLaw security).weight blur|) ≤
      2 / (2 : ℝ)^bits := by
    apply hprod.trans
    exact (add_le_add hscalar hscalar).trans_eq (by ring)
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
      (diffusePairAt security primary source).weight (first, second)| ≤ 2 / (2 : ℝ)^bits := by
  have hwidth : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [DiffuseProfiles.anchorWidth_eq, Parameters.base]
  have hcutoff : ((security + 2)^2 - 1) / 2 = edgeCutoff security := by
    simp only [edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  unfold current
  rw [PublicParameterProgram.modulus_value, hwidth, hcutoff]
  exact evaluate_error security bits primary first second source

end
end CurrentAFT.LocalDiffuseProgram

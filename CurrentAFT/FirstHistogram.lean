import CurrentAFT.ProposalSymmetry
import CurrentAFT.BackgroundCertificates
import AFT.TrimmedPair
import AFT.FiniteExpectationAlgebra

/-!
# The first histogram of the actual protected leg reference experiment

The reference law below retains the protected second scalar beside the
ordered endpoint pair. The diffuse law is the true integer trimmed slice,
with its varying denominator. The marked companion uses that same second
scalar with a minus sign, together with the independent actual public blur.
Only laws of outputs are constructed here. Implementing them by one public
law of local affine charts is a separate proof obligation.
-/

namespace CurrentAFT.FirstHistogram

open AFT DiffuseProfiles ProposalPrimary PairedResponse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  actualSeedLaw actualProfile activation primaryLaw centerLaw InwardAnchor.smoothedAnchorLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)
abbrev Pair (security : ℕ) := Palette security × Palette security
abbrev Scalar (security : ℕ) := InwardAnchor.ScalarSample security
abbrev JointOutput (security : ℕ) := Scalar security × Pair security

private theorem expectation_mix {Input Output : Type*} [Fintype Input] [Fintype Output]
    (law : FiniteDist Input) (kernel : Input → FiniteDist Output) (value : Output → ℝ) :
    (law.mix kernel).expectation value = law.expectation (fun input => (kernel input).expectation value) := by
  simp only [FiniteDist.expectation, FiniteDist.mix_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

def atom {Color : Type*} [DecidableEq Color] (first second : Color) : ℝ :=
  if first = second then 1 else 0

private theorem expectation_atom {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist Color) (color : Color) : law.expectation (fun input => atom input color) = law.weight color := by
  classical
  simp [FiniteDist.expectation, atom, mul_ite]

def endpointHistogram (security : ℕ) (law : FiniteDist (JointOutput security)) (output : Palette security) : ℝ :=
  law.expectation (fun sample => atom sample.2.1 output + atom sample.2.2 output)

private theorem diffuse_clearance (security : ℕ) :
    2 + (2 * (Parameters.anchorWidth security : ℤ) + ((Parameters.sourceCutoff security : ℤ) - 1)) +
        ((Parameters.sourceCutoff security : ℤ) - 1) < Parameters.modulus security := by
  have h := deletion_clearance security
  simp only [deletion] at h
  omega

/-- A fixed protected seed still retains the same second scalar in the
integer pair sum. The uniform offset ranges over the printed signed
anchor interval. -/
def diffuseSeedPair (security : ℕ) (positive : Bool) (seed : ActualSeed security) : FiniteDist (Pair security) :=
  TrimmedSlice.mixedPairDistribution (Parameters.modulus security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + ((Parameters.sourceCutoff security : ℤ) - 1))
    ((Parameters.sourceCutoff security : ℤ) - 1) (Parameters.anchorWidth security)
    (InwardAnchor.anchorWidth_pos security).ne'
    (fun _ : Unit => intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
    (fun _ : Unit => actualSecond security seed) (FiniteDist.uniform Unit) (by norm_num)
    (fun _ _ hin => interval_bound positive _ _ _ _ (actualBlur_bound security seed) hin)
    (fun _ => actualSecond_bound security seed) (diffuse_clearance security)

theorem diffuseSeedPair_weight (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (first second : Palette security) :
    (diffuseSeedPair security positive seed).weight (first, second) =
      TrimmedSlice.averagedPair (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) first second := by
  simp [diffuseSeedPair, TrimmedSlice.mixedPairDistribution, TrimmedSlice.mixedPair]

theorem diffuseSeedPair_first (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (diffuseSeedPair security positive seed).expectation (fun pair => atom pair.1 output) =
      TrimmedSlice.averagedLaw (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) output.val := by
  classical
  simp only [FiniteDist.expectation, Fintype.sum_prod_type, diffuseSeedPair_weight]
  rw [Finset.sum_comm]
  simp only [atom, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold TrimmedSlice.averagedPair TrimmedSlice.averagedLaw TrimmedSlice.intervalMixture
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro offset _
  rw [← Finset.mul_sum, TrimmedSlice.orderedPairSlice_marginal _ _ _ (by norm_num)]

theorem diffuseSeedPair_second (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (diffuseSeedPair security positive seed).expectation (fun pair => atom pair.2 output) =
      TrimmedSlice.averagedLaw (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) output.val := by
  classical
  have hsymm (first second : Palette security) :
      (diffuseSeedPair security positive seed).weight (first, second) =
        (diffuseSeedPair security positive seed).weight (second, first) := by
    rw [diffuseSeedPair_weight, diffuseSeedPair_weight]
    simp only [TrimmedSlice.averagedPair, TrimmedSlice.orderedPairSlice_symmetric]
  rw [← diffuseSeedPair_first security positive seed output]
  simp only [FiniteDist.expectation, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [hsymm]

/-- The actual diffuse reference keeps the source increment beside the
pair. Its direction reads the primary color and the fresh midpoint coin. -/
def diffuseReferenceLaw (security : ℕ) (primary : Palette security) : FiniteDist (JointOutput security) :=
  (FiniteDist.uniform Bool).mix (fun coin =>
    (actualSeedLaw security).mix (fun seed =>
      (diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) seed).map
        (fun pair => (seed.2, pair))))

def diffuseMarginal (security : ℕ) (primary output : Palette security) : ℝ :=
  (FiniteDist.uniform Bool).expectation (fun coin =>
    actualProfile security (InwardAnchor.positiveDirection security primary coin) output)

theorem diffuseReference_histogram (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (diffuseReferenceLaw security primary) output =
      2 * diffuseMarginal security primary output := by
  unfold endpointHistogram diffuseReferenceLaw
  rw [expectation_mix]
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def,
    FiniteDist.expectation_add, diffuseSeedPair_first, diffuseSeedPair_second]
  unfold diffuseMarginal actualProfile profile TrimmedSlice.mixedLaw
  simp only [FiniteDist.expectation]
  ring

theorem diffuse_histogram_decomposition (security : ℕ) (primary output : Palette security) :
    2 * (1 - activation security) * diffuseMarginal security primary output =
      2 * (1 - activation security) * diffuseMean security output +
        signProfile security output * FirstResponse.anchorSign security primary := by
  unfold diffuseMarginal
  simp only [FiniteDist.expectation, FiniteDist.uniform_weight, Fintype.card_bool,
    Nat.cast_ofNat, Fintype.sum_bool]
  by_cases hl : 2 * primary.val < Parameters.modulus security - 1
  · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, if_true]
    unfold diffuseMean signProfile
    ring
  · by_cases hh : Parameters.modulus security - 1 < 2 * primary.val
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false, if_true]
      unfold diffuseMean signProfile
      ring
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false]
      unfold diffuseMean signProfile
      ring

private theorem negativeSecond_bound (security : ℕ) (seed : ActualSeed security) :
    |-(actualSecond security seed)| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  simpa only [abs_neg] using actualSecond_bound security seed

/-- Activation fixes the marked endpoint and preserves the same second
source, with its negative sign in the companion. Public blur is sampled
independently from the actual edge-difference law. -/
def markedReferenceLaw (security : ℕ) (primary : Palette security) : FiniteDist (JointOutput security) :=
  (actualSeedLaw security).mix (fun seed =>
    (InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed)
      (negativeSecond_bound security seed)).map (fun companion =>
        (seed.2, (primary, shiftEquiv security (actualBlur security seed) companion))))

def markedCompanion (security : ℕ) (primary output : Palette security) : ℝ :=
  (actualSeedLaw security).expectation (fun seed =>
    ((InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed)
      (negativeSecond_bound security seed)).map
      (shiftEquiv security (actualBlur security seed))).weight output)

theorem markedReference_histogram (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (markedReferenceLaw security primary) output =
      atom primary output + markedCompanion security primary output := by
  unfold endpointHistogram markedReferenceLaw markedCompanion
  rw [expectation_mix]
  simp_rw [FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_add,
    FiniteDist.expectation_const]
  simp only [FiniteDist.expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro seed _
  congr 1
  change (InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed) _).expectation
      (fun companion => atom (shiftEquiv security (actualBlur security seed) companion) output) = _
  rw [← expectation_atom ((InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed)
    (negativeSecond_bound security seed)).map (shiftEquiv security (actualBlur security seed))) output]
  rw [FiniteDist.expectation_map]
  rfl

/-- The protected reference mixture after averaging the activation event.
Both branches retain the same second-source marginal. -/
def referenceLaw (security : ℕ) (primary : Palette security) : FiniteDist (JointOutput security) where
  weight sample := (1 - activation security) * (diffuseReferenceLaw security primary).weight sample +
    activation security * (markedReferenceLaw security primary).weight sample
  nonneg sample := add_nonneg
    (mul_nonneg (by linarith [activation_le_half security]) ((diffuseReferenceLaw security primary).nonneg sample))
    (mul_nonneg (activation_pos security).le ((markedReferenceLaw security primary).nonneg sample))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, FiniteDist.sum_one, FiniteDist.sum_one]
    ring

theorem reference_histogram (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (referenceLaw security primary) output =
      activation security * atom primary output + activation security * markedCompanion security primary output +
        2 * (1 - activation security) * diffuseMean security output +
          signProfile security output * FirstResponse.anchorSign security primary := by
  have hmix : endpointHistogram security (referenceLaw security primary) output =
      (1 - activation security) * endpointHistogram security (diffuseReferenceLaw security primary) output +
        activation security * endpointHistogram security (markedReferenceLaw security primary) output := by
    simp only [endpointHistogram, FiniteDist.expectation, referenceLaw, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [hmix, diffuseReference_histogram, markedReference_histogram]
  have hdiff := diffuse_histogram_decomposition security primary output
  nlinarith only [hdiff]

/-- Reflection of the second source alone preserves the actual product
law and leaves the two public edge scalars fixed. -/
def secondNegate (security : ℕ) : ActualSeed security ≃ ActualSeed security :=
  (Equiv.refl _).prodCongr
    (GaussianSource.windowNegateEquiv (Parameters.sourceCutoff security - 1))

theorem secondNegate_weight (security : ℕ) (seed : ActualSeed security) :
    (actualSeedLaw security).weight (secondNegate security seed) = (actualSeedLaw security).weight seed := by
  simp only [actualSeedLaw, secondNegate, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, FiniteDist.prod_weight, scalarLaw, GaussianSource.windowGaussian_reflection]

theorem secondNegate_blur (security : ℕ) (seed : ActualSeed security) :
    actualBlur security (secondNegate security seed) = actualBlur security seed := rfl

theorem secondNegate_second (security : ℕ) (seed : ActualSeed security) :
    actualSecond security (secondNegate security seed) = -actualSecond security seed := rfl

theorem markedCompanion_convolution (security : ℕ) (primary output : Palette security) :
    markedCompanion security primary output =
      BackgroundCertificates.rootConvolutionProfile security
        (InwardAnchor.smoothedAnchorLaw security primary).weight output := by
  unfold markedCompanion
  simp only [FiniteDist.expectation, FiniteDist.map_equiv_weight]
  calc
    _ = ∑ seed, (actualSeedLaw security).weight seed *
        (InwardAnchor.shiftedAnchorLaw security primary (actualSecond security seed)
          (actualSecond_bound security seed)).weight
            ((shiftEquiv security (actualBlur security seed)).symm output) := by
      calc
        _ = ∑ seed, (actualSeedLaw security).weight (secondNegate security seed) *
          (InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security (secondNegate security seed))
            (negativeSecond_bound security (secondNegate security seed))).weight
              ((shiftEquiv security (actualBlur security (secondNegate security seed))).symm output) :=
          ((secondNegate security).sum_comp _).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro seed _
          simp only [secondNegate_weight, secondNegate_second, secondNegate_blur, neg_neg]
    _ = ((edgeLaw security).prod (edgeLaw security)).expectation (fun edge =>
        (InwardAnchor.smoothedAnchorLaw security primary).weight
          ((shiftEquiv security ((edge.1 : ℤ) - edge.2)).symm output)) := by
      change (actualSeedLaw security).expectation (fun seed =>
        (InwardAnchor.shiftedAnchorLaw security primary (actualSecond security seed)
          (actualSecond_bound security seed)).weight
            ((shiftEquiv security (actualBlur security seed)).symm output)) = _
      rw [actualSeedLaw, FiniteDist.expectation_prod]
      simp only [actualSecond, actualBlur, InwardAnchor.smoothedAnchorLaw, FiniteDist.mix_weight,
        FiniteDist.expectation]
    _ = _ := by
      change _ = (actualSeedLaw security).expectation (fun seed =>
        (InwardAnchor.smoothedAnchorLaw security primary).weight
          ((shiftEquiv security (actualBlur security seed)).symm output))
      conv_rhs => rw [actualSeedLaw, FiniteDist.expectation_prod]
      simp only [actualBlur, FiniteDist.expectation_const]

/-- The fixed-primary physical first histogram, now with the actual
smoothed-anchor/body convolution rather than an abstract companion. -/
theorem reference_histogram_convolution (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (referenceLaw security primary) output =
      activation security * atom primary output + activation security *
        BackgroundCertificates.rootConvolutionProfile security
          (InwardAnchor.smoothedAnchorLaw security primary).weight output +
        2 * (1 - activation security) * diffuseMean security output +
          signProfile security output * FirstResponse.anchorSign security primary := by
  rw [reference_histogram, markedCompanion_convolution]

theorem actualSecond_expectation (security : ℕ) (value : Scalar security → ℝ) :
    (actualSeedLaw security).expectation (fun seed => value seed.2) =
      (scalarLaw security).expectation value := by
  rw [actualSeedLaw, FiniteDist.expectation_prod]
  change ((edgeLaw security).prod (edgeLaw security)).expectation
    (fun _ => (scalarLaw security).expectation value) = _
  rw [FiniteDist.expectation_const]

theorem diffuse_attachment_expectation (security : ℕ) (primary : Palette security)
    (value : Scalar security → ℝ) :
    (diffuseReferenceLaw security primary).expectation (fun sample => value sample.1) =
      (scalarLaw security).expectation value := by
  unfold diffuseReferenceLaw
  rw [expectation_mix]
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_const,
    actualSecond_expectation]

theorem marked_attachment_expectation (security : ℕ) (primary : Palette security)
    (value : Scalar security → ℝ) :
    (markedReferenceLaw security primary).expectation (fun sample => value sample.1) =
      (scalarLaw security).expectation value := by
  unfold markedReferenceLaw
  rw [expectation_mix]
  simp_rw [FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_const]
  exact actualSecond_expectation security value

theorem reference_expectation (security : ℕ) (primary : Palette security)
    (value : JointOutput security → ℝ) :
    (referenceLaw security primary).expectation value =
      (1 - activation security) * (diffuseReferenceLaw security primary).expectation value +
        activation security * (markedReferenceLaw security primary).expectation value := by
  simp only [FiniteDist.expectation, referenceLaw, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- The protected attachment increment has its genuine scalar law,
independently of the primary color and the activation branch. -/
theorem reference_attachment_expectation (security : ℕ) (primary : Palette security)
    (value : Scalar security → ℝ) :
    (referenceLaw security primary).expectation (fun sample => value sample.1) =
      (scalarLaw security).expectation value := by
  rw [reference_expectation, diffuse_attachment_expectation, marked_attachment_expectation]
  ring

def scoreProfile (security : ℕ) (score : Palette security → ℝ) : Palette security → ℝ :=
  fun primary => (primaryLaw security).weight primary * score primary

private theorem sum_atom (security : ℕ) (profile : Palette security → ℝ) (output : Palette security) :
    (∑ primary, profile primary * atom primary output) = profile output := by
  classical
  simp [atom, mul_ite]

theorem convolution_sum (security : ℕ) (coefficient : Palette security → ℝ)
    (kernel : Palette security → Palette security → ℝ) (output : Palette security) :
    (∑ primary, coefficient primary * BackgroundCertificates.rootConvolutionProfile security (kernel primary) output) =
      BackgroundCertificates.rootConvolutionProfile security
        (fun center => ∑ primary, coefficient primary * kernel primary center) output := by
  unfold BackgroundCertificates.rootConvolutionProfile
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro seed _
  apply Finset.sum_congr rfl
  intro primary _
  ring

theorem markedCompanion_score (security : ℕ) (score : Palette security → ℝ)
    (output : Palette security) :
    (∑ primary, scoreProfile security score primary * markedCompanion security primary output) =
      BackgroundCertificates.rootConvolutionProfile security (anchorWeightedScore security score) output := by
  simp_rw [markedCompanion_convolution]
  rw [convolution_sum]
  congr 1
  funext center
  unfold anchorWeightedScore scoreProfile
  apply Finset.sum_congr rfl
  intro primary _
  ring

def primaryHistogramResponse (security : ℕ) (score : Palette security → ℝ) (output : Palette security) : ℝ :=
  ∑ primary, scoreProfile security score primary * endpointHistogram security (referenceLaw security primary) output

/-- The signed primary response is derived from the concrete joint law.
The independent attachment contributes zero for every centered score. -/
theorem primaryHistogramResponse_formula (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (output : Palette security) :
    primaryHistogramResponse security score output =
      activation security * scoreProfile security score output +
        activation security * BackgroundCertificates.rootConvolutionProfile security
          (anchorWeightedScore security score) output +
        signProfile security output * signFunctional (FirstResponse.anchorSign security) (scoreProfile security score) := by
  unfold primaryHistogramResponse
  simp_rw [reference_histogram]
  calc
    _ = ∑ primary,
        (activation security * (scoreProfile security score primary * atom primary output) +
          activation security * (scoreProfile security score primary * markedCompanion security primary output) +
          (2 * (1 - activation security) * diffuseMean security output) * scoreProfile security score primary +
          signProfile security output *
            (FirstResponse.anchorSign security primary * scoreProfile security score primary)) := by
      apply Finset.sum_congr rfl
      intro primary _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_atom, markedCompanion_score]
      change _ + _ + _ * (∑ primary, (primaryLaw security).weight primary * score primary) + _ = _
      rw [hcentered, mul_zero, add_zero]
      rfl

theorem primary_attachment_response_zero (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (value : Scalar security → ℝ) :
    (∑ primary, (primaryLaw security).weight primary * score primary *
      (referenceLaw security primary).expectation (fun sample => value sample.1)) = 0 := by
  simp only [reference_attachment_expectation, ← Finset.sum_mul, hcentered, zero_mul]

/-- A reserved compensator center has the actual ordinary body channel,
using the independent protected edge difference. -/
def compensatorBodyLaw (security : ℕ) (center : Palette security) : FiniteDist (Palette security) :=
  (actualSeedLaw security).map (fun seed => shiftEquiv security (actualBlur security seed) center)

theorem compensatorBodyLaw_weight (security : ℕ) (center output : Palette security) :
    (compensatorBodyLaw security center).weight output =
      BackgroundCertificates.rootConvolutionProfile security (atom center) output := by
  unfold compensatorBodyLaw BackgroundCertificates.rootConvolutionProfile
  rw [FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro seed _
  have heq : (shiftEquiv security (actualBlur security seed)) center = output ↔
      center = (shiftEquiv security (actualBlur security seed)).symm output := by
    exact (Equiv.eq_symm_apply _).symm
  simp only [heq, atom]
  split_ifs <;> ring

theorem body_score_convolution (security : ℕ) (coefficient : Palette security → ℝ)
    (output : Palette security) :
    (∑ center, coefficient center * (compensatorBodyLaw security center).weight output) =
      BackgroundCertificates.rootConvolutionProfile security coefficient output := by
  simp_rw [compensatorBodyLaw_weight]
  rw [convolution_sum]
  congr 1
  funext center
  exact sum_atom security coefficient center

theorem center_weight_compensator (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) :
    (centerLaw security).weight center * compensatorScore security score center =
      activation security * anchorWeightedScore security score center := by
  unfold compensatorScore
  by_cases hzero : (centerLaw security).weight center = 0
  · rw [hzero, centerLaw_zero_implies_anchorScore_zero security score center hzero]
    ring
  · field_simp

theorem compensatorHistogramResponse_formula (security : ℕ) (score : Palette security → ℝ)
    (output : Palette security) :
    (∑ center, (centerLaw security).weight center * compensatorScore security score center *
      (compensatorBodyLaw security center).weight output) =
      activation security * BackgroundCertificates.rootConvolutionProfile security
        (anchorWeightedScore security score) output := by
  simp only [center_weight_compensator, mul_assoc, ← Finset.mul_sum]
  rw [body_score_convolution]

/-- The complete first histogram reads the two actual off-body outputs
and the reserved compensator-body output. Any remaining coordinate has a
profile independent of this public pair and is integrated in `other`.
Their hidden roots may be correlated: only first marginals enter here. -/
def completeHistogramResponse (security : ℕ) (score : Palette security → ℝ)
    (other : Palette security → ℝ) (output : Palette security) : ℝ :=
  ∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
    pairedScore security score primary center *
      (endpointHistogram security (referenceLaw security primary) output +
        (compensatorBodyLaw security center).weight output + other output)

theorem completeHistogramResponse_decomposition (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (other : Palette security → ℝ) (output : Palette security) :
    completeHistogramResponse security score other output =
      primaryHistogramResponse security score output -
        ∑ center, (centerLaw security).weight center * compensatorScore security score center *
          (compensatorBodyLaw security center).weight output := by
  have hcompensator : (∑ center, (centerLaw security).weight center * compensatorScore security score center) = 0 := by
    rw [compensatorScore_mass, hcentered, mul_zero]
  have hleg (primary : Palette security) :
      (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center *
          endpointHistogram security (referenceLaw security primary) output) =
        scoreProfile security score primary * endpointHistogram security (referenceLaw security primary) output := by
    unfold pairedScore scoreProfile
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    calc
      _ = ((primaryLaw security).weight primary * score primary *
            endpointHistogram security (referenceLaw security primary) output) *
              (∑ center, (centerLaw security).weight center) -
          ((primaryLaw security).weight primary * endpointHistogram security (referenceLaw security primary) output) *
            (∑ center, (centerLaw security).weight center * compensatorScore security score center) := by
        simp only [Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro center _ <;> ring
      _ = _ := by rw [FiniteDist.sum_one, hcompensator]; ring
  have hbody : (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center * (compensatorBodyLaw security center).weight output) =
      -(∑ center, (centerLaw security).weight center * compensatorScore security score center *
        (compensatorBodyLaw security center).weight output) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ center, (((centerLaw security).weight center * (compensatorBodyLaw security center).weight output) *
          (∑ primary, (primaryLaw security).weight primary * score primary) -
        ((centerLaw security).weight center * compensatorScore security score center *
          (compensatorBodyLaw security center).weight output) * (∑ primary, (primaryLaw security).weight primary)) := by
        apply Finset.sum_congr rfl
        intro center _
        unfold pairedScore
        simp only [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro primary _
        ring
      _ = _ := by simp only [hcentered, mul_zero, FiniteDist.sum_one, mul_one, zero_sub, Finset.sum_neg_distrib]
  have hother : (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center * other output) = 0 := by
    simp only [← Finset.sum_mul, pairedScore_mean_zero security score hcentered, zero_mul]
  unfold completeHistogramResponse
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [hleg]
  rw [hbody, hother, add_zero]
  rfl

/-- The genuine paired primary and compensator cancel the entire actual
companion term. The remaining physical histogram is exactly activation
times the previously constructed rank-one response. -/
theorem completeHistogramResponse_eq_activation_response (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (other : Palette security → ℝ) (output : Palette security) :
    completeHistogramResponse security score other output =
      activation security * FirstResponse.response security (scoreProfile security score) output := by
  rw [completeHistogramResponse_decomposition security score hcentered,
    primaryHistogramResponse_formula security score hcentered, compensatorHistogramResponse_formula]
  simp only [FirstResponse.response, primaryRankOperator_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    profileSignMap]
  change _ = activation security * (scoreProfile security score output +
    ((activation security)⁻¹ * signFunctional (FirstResponse.anchorSign security) (scoreProfile security score)) *
      signProfile security output)
  have hactivation := (activation_pos security).ne'
  field_simp
  ring

theorem anchorSign_reflection (security : ℕ) (color : Palette security) :
    FirstResponse.anchorSign security color.rev = -FirstResponse.anchorSign security color := by
  have hsum : color.rev.val + color.val = Parameters.modulus security - 1 := by
    simp only [Fin.val_rev]
    omega
  by_cases hl : 2 * color.val < Parameters.modulus security - 1
  · have hrl : ¬2 * color.rev.val < Parameters.modulus security - 1 := by omega
    have hrh : Parameters.modulus security - 1 < 2 * color.rev.val := by omega
    simp only [FirstResponse.anchorSign, hl, hrl, hrh, if_true, if_false]
    ring
  · by_cases hh : Parameters.modulus security - 1 < 2 * color.val
    · have hrl : 2 * color.rev.val < Parameters.modulus security - 1 := by omega
      simp only [FirstResponse.anchorSign, hl, hh, hrl, if_false, if_true]
    · have hrl : ¬2 * color.rev.val < Parameters.modulus security - 1 := by omega
      have hrh : ¬Parameters.modulus security - 1 < 2 * color.rev.val := by omega
      simp only [FirstResponse.anchorSign, hl, hh, hrl, hrh, if_false, neg_zero]

theorem primary_anchorSign_mean_zero (security : ℕ) :
    (∑ primary, (primaryLaw security).weight primary * FirstResponse.anchorSign security primary) = 0 := by
  have hreflection :
      (∑ primary, (primaryLaw security).weight primary * FirstResponse.anchorSign security primary) =
        -(∑ primary, (primaryLaw security).weight primary * FirstResponse.anchorSign security primary) := by
    calc
      _ = ∑ primary : Palette security, (primaryLaw security).weight primary.rev * FirstResponse.anchorSign security primary.rev :=
        (Equiv.sum_comp (Fin.revPerm : Palette security ≃ Palette security) _).symm
      _ = _ := by simp only [ProposalSymmetry.primaryLaw_reflection, anchorSign_reflection, mul_neg,
        Finset.sum_neg_distrib]
  linarith

/-- The unweighted actual leg includes its two off-body outputs and its
attachment output, whose center has the ordinary smoothed body law. -/
def legFirstMean (security : ℕ) (output : Palette security) : ℝ :=
  (∑ primary, (primaryLaw security).weight primary *
      endpointHistogram security (referenceLaw security primary) output) +
    (bodyLaw security true).weight output

theorem legFirstMean_formula (security : ℕ) (output : Palette security) :
    legFirstMean security output =
      activation security * (primaryLaw security).weight output +
        activation security * BackgroundCertificates.rootConvolutionProfile security
          (anchorPrimaryLaw security).weight output +
        (bodyLaw security true).weight output + 2 * (1 - activation security) * diffuseMean security output := by
  have hcompanion : (∑ primary, (primaryLaw security).weight primary * markedCompanion security primary output) =
      BackgroundCertificates.rootConvolutionProfile security (anchorPrimaryLaw security).weight output := by
    simp_rw [markedCompanion_convolution]
    rw [convolution_sum]
    rfl
  unfold legFirstMean
  simp_rw [reference_histogram]
  calc
    _ = (∑ primary,
        (activation security * ((primaryLaw security).weight primary * atom primary output) +
          activation security * ((primaryLaw security).weight primary * markedCompanion security primary output) +
          (2 * (1 - activation security) * diffuseMean security output) * (primaryLaw security).weight primary +
          signProfile security output *
            ((primaryLaw security).weight primary * FirstResponse.anchorSign security primary))) +
        (bodyLaw security true).weight output := by
      congr 1
      apply Finset.sum_congr rfl
      intro primary _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_atom, hcompanion,
        FiniteDist.sum_one, mul_one, primary_anchorSign_mean_zero, mul_zero, add_zero]
      ring

theorem convolvedCenterLaw_formula (security : ℕ) (output : Palette security) :
    (BackgroundCertificates.convolvedCenterLaw security).weight output =
      (1 + compensation security) * (bodyLaw security false).weight output -
        compensation security * BackgroundCertificates.rootConvolutionProfile security
          (anchorPrimaryLaw security).weight output := by
  rw [BackgroundCertificates.convolvedCenterLaw_weight]
  unfold centerLaw
  change BackgroundCertificates.rootConvolutionProfile security (centerProfile security) output = _
  rw [BackgroundCertificates.bodyLaw_false_weight]
  simp only [BackgroundCertificates.rootConvolutionProfile, centerProfile, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro seed _ <;> ring

/-- Actual first-moment balancing, using the current primary balancing
formula and the constructed center law. This is the physical identity
needed by the leg's linear background certificate. -/
theorem baseline_first_histogram (security : ℕ) (output : Palette security) :
    freeMass security *
        ((BackgroundCertificates.convolvedCenterLaw security).weight output - FringeCertificate.uniformProfile security output) +
      (Parameters.modulus security : ℝ) *
        ((bodyLaw security true).weight output - FringeCertificate.uniformProfile security output) +
      (Parameters.legCount security : ℝ) *
        (legFirstMean security output - 3 * FringeCertificate.uniformProfile security output) = 0 := by
  rw [legFirstMean_formula, convolvedCenterLaw_formula]
  have hmark := (markMass_pos security).ne'
  have hfree := (freeMass_pos security).ne'
  have hq := (FirstResponse.modulus_pos security).ne'
  simp only [primaryLaw]
  unfold primaryProfile compensation FringeCertificate.uniformProfile
  field_simp [hmark, hfree, hq]
  simp only [markMass, freeMass, Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end

end CurrentAFT.FirstHistogram

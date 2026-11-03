import CurrentAFT.LocalDiffuseProgram
import CurrentAFT.LocalMarkedProgram

/-! # The actual current pair entry, including its computed activation

The protected scalar remains one retained argument. Both branches use
the same current public Gaussian approximation; activation is computed
from the current scalar window's zero atom. The error is simultaneous
in the public primary and both physical endpoint colors.
-/
namespace CurrentAFT.LocalPairProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def activationApprox (security bits : ℕ) : ℚ :=
  (1 / 2 : ℚ) * windowApproxWeight (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceCutoff security - 1) bits (windowZero (Parameters.sourceCutoff security - 1))

def current (security bits primary : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  let rate := activationApprox security bits
  (1-rate) * LocalDiffuseProgram.current security bits primary source first second +
    rate * LocalMarkedProgram.current security bits primary source first second

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw

theorem activationApprox_bounds (security bits : ℕ) :
    0 ≤ (activationApprox security bits : ℝ) ∧ (activationApprox security bits : ℝ) ≤ 1/2 := by
  let law := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
  have hp := law.nonneg (windowZero (Parameters.sourceCutoff security - 1))
  have hu := law.atom_le_one (windowZero (Parameters.sourceCutoff security - 1))
  have heq : (activationApprox security bits : ℝ) = (1/2:ℝ)*law.weight (windowZero _) := by
    simp only [activationApprox, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rfl
  rw [heq]
  change 0 ≤ (1/2:ℝ) * law.weight (windowZero _) ∧ (1/2:ℝ) * law.weight (windowZero _) ≤ 1/2
  constructor <;> linarith

theorem activationApprox_error (security bits : ℕ) :
    |(activationApprox security bits : ℝ) - DiffuseProfiles.activation security| ≤ (1/2:ℝ) * (1 / (2:ℝ)^bits) := by
  let law := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
  have hsum : (∑ point, |law.weight point - (scalarLaw security).weight point|) ≤ 1 / (2:ℝ)^bits :=
    windowApproxLaw_l1 _ _ _ _ (WindowGaussianSampler.squaredWidth_positive security)
      (WindowGaussianSampler.squaredWidth_real security).symm
  have hatom := Finset.single_le_sum (f := fun point => |law.weight point - (scalarLaw security).weight point|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (windowZero (Parameters.sourceCutoff security - 1)))
  have heq : (activationApprox security bits : ℝ) = (1/2:ℝ)*law.weight (windowZero _) := by
    simp only [activationApprox, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rfl
  rw [heq]
  unfold DiffuseProfiles.activation
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  exact mul_le_mul_of_nonneg_left (hatom.trans hsum) (by norm_num)

theorem current_error (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) :
    |(current security bits primary.val source.val first.val second.val : ℝ) -
      (pairAt security primary source).weight (first, second)| ≤ 3 / (2:ℝ)^bits := by
  let rate : ℝ := activationApprox security bits
  let diffuse : ℝ := LocalDiffuseProgram.current security bits primary.val source.val first.val second.val
  let marked : ℝ := LocalMarkedProgram.current security bits primary.val source.val first.val second.val
  let trueDiffuse := (diffusePairAt security primary source).weight (first, second)
  let trueMarked := (markedPairAt security primary source).weight (first, second)
  have hr := activationApprox_bounds security bits
  have hrate : 0 ≤ rate ∧ rate ≤ 1/2 := hr
  have hcompl : 0 ≤ 1-rate := by linarith only [hrate.2]
  have hd := LocalDiffuseProgram.current_error security bits primary first second source
  have hm := LocalMarkedProgram.current_error security bits primary first second source
  have ha := activationApprox_error security bits
  have hdiffuse : |trueDiffuse| ≤ 1 := by
    rw [abs_of_nonneg ((diffusePairAt security primary source).nonneg _)]
    exact (diffusePairAt security primary source).atom_le_one _
  have hmarked : |trueMarked| ≤ 1 := by
    rw [abs_of_nonneg ((markedPairAt security primary source).nonneg _)]
    exact (markedPairAt security primary source).atom_le_one _
  have hgap : |trueMarked - trueDiffuse| ≤ 2 := by
    exact (abs_sub _ _).trans (by linarith only [hdiffuse, hmarked])
  unfold current
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  change |(1-rate)*diffuse + rate*marked -
    ((1-DiffuseProfiles.activation security)*trueDiffuse + DiffuseProfiles.activation security*trueMarked)| ≤ _
  calc
    _ = |(1-rate)*(diffuse-trueDiffuse) + rate*(marked-trueMarked) +
        (rate-DiffuseProfiles.activation security)*(trueMarked-trueDiffuse)| := by congr 1; ring
    _ ≤ |(1-rate)*(diffuse-trueDiffuse)| + |rate*(marked-trueMarked)| +
        |(rate-DiffuseProfiles.activation security)*(trueMarked-trueDiffuse)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (1-rate) * |diffuse-trueDiffuse| + rate * |marked-trueMarked| +
        |rate-DiffuseProfiles.activation security| * |trueMarked-trueDiffuse| := by
      rw [abs_mul, abs_of_nonneg hcompl, abs_mul, abs_of_nonneg hrate.1, abs_mul]
    _ ≤ (1-rate)*(2/(2:ℝ)^bits) + rate*(2/(2:ℝ)^bits) + ((1/2:ℝ)*(1/(2:ℝ)^bits))*2 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hd hcompl)
        (mul_le_mul_of_nonneg_left hm hrate.1))
        (mul_le_mul ha hgap (abs_nonneg _) (by positivity))
    _ = _ := by ring

end
end CurrentAFT.LocalPairProgram

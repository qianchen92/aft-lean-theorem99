import CurrentAFT.RationalMassLiftProgram
import CurrentAFT.RationalBackgroundProfiles
import CurrentAFT.RootReferenceColumns
import CurrentAFT.RationalRootMassProgram

/-! # Rational actual shifted and mean body profiles for every role

The root mean uses the same protected two-edge blur as the construction.
Free, attachment and queue profiles retain their original laws, including
the one attachment scalar and the fixed common queue.
-/
namespace CurrentAFT.RationalRootProfileProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  RootTaggedLocal
open UniformBodyProfiles (BodyRole preRootLaw)
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def attachment (security bits output : ℕ) : ℚ :=
  ∑ scalar : Window ((security + 2)^2 - 1),
    RationalProposalProgram.gaussianWeight security ((security + 2)^2 - 1) bits scalar *
      RationalBackgroundProfiles.shifted security scalar.val output

def preRoot (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : ℕ) : ℚ :=
  match role with
  | .free => RationalProposalProgram.center security bits output
  | .attachment => attachment security bits output
  | .queue => RationalBackgroundProfiles.shifted security queue output

def shifted (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : ℕ) : ℚ :=
  preRoot security bits role queue (RationalBackgroundProfiles.inverseShift security root output)

def mean (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : ℕ) : ℚ :=
  RationalBackgroundProfiles.convolution security bits (preRoot security bits role queue) output

def deviation (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : ℕ) : ℚ :=
  shifted security bits role queue root output - mean security bits role queue output

def meanDeviation (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : ℕ) : ℚ :=
  mean security bits role queue output - 1 / (PublicParameterProgram.modulus security).count

def firstDensity (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (deviation security bits role queue root) output

def meanDensity (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (meanDeviation security bits role queue) output

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base primaryLaw centerLaw

def approximatePreRoot (security bits : ℕ) (role : BodyRole) (queue : ℤ) : FiniteDist (Palette security) :=
  match role with
  | .free => RationalProposalProgram.approximateCenterLaw security bits
  | .attachment =>
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits).mix
        (fun scalar => (safeLaw security).map (shiftEquiv security scalar.val))
  | .queue => (safeLaw security).map (shiftEquiv security queue)

theorem preRoot_cast (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    (preRoot security bits role queue output.val : ℝ) = (approximatePreRoot security bits role queue).weight output := by
  cases role with
  | free => rfl
  | queue => exact RationalBackgroundProfiles.shifted_cast security queue output
  | attachment =>
    have hcutoff : (security + 2)^2 - 1 = Parameters.sourceCutoff security - 1 := by
      simp only [Parameters.sourceCutoff, Parameters.base]
    unfold preRoot attachment
    rw [hcutoff]
    simp only [Rat.cast_sum, Rat.cast_mul, RationalProposalProgram.gaussianWeight_eq,
      RationalBackgroundProfiles.shifted_cast, approximatePreRoot, FiniteDist.mix_weight, windowApproxLaw]
    rfl

theorem preRoot_bound (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    |(preRoot security bits role queue output.val : ℝ)| ≤ 1 := by
  rw [preRoot_cast, abs_of_nonneg ((approximatePreRoot security bits role queue).nonneg output)]
  exact (approximatePreRoot security bits role queue).atom_le_one output

def preRootError (security : ℕ) : ℝ :=
  RationalRootMassProgram.primaryErrorConstant security * Parameters.modulus security + 3

theorem preRootError_one_le (security : ℕ) : 1 ≤ preRootError security := by
  have h : 0 ≤ RationalRootMassProgram.primaryErrorConstant security * (Parameters.modulus security : ℝ) := by
    unfold RationalRootMassProgram.primaryErrorConstant
    positivity
  unfold preRootError
  linarith

theorem preRoot_error (security bits : ℕ) (role : BodyRole) (queue : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(preRoot security bits role queue output.val : ℝ) - (preRootLaw security role queue).weight output| ≤
      preRootError security * (1 / (2 : ℝ)^bits) := by
  have he : 0 ≤ 1 / (2 : ℝ)^bits := by positivity
  cases role with
  | free =>
    have h := RationalProposalProgram.center_error security bits output hprecision hbudget
    have hsame : |(preRoot security bits .free queue output.val : ℝ) - (preRootLaw security .free queue).weight output| ≤
        (RationalRootMassProgram.primaryErrorConstant security * Parameters.modulus security + 2) * (1 / (2 : ℝ)^bits) := by
      simpa only [preRoot, preRootLaw, centerLaw, RationalRootMassProgram.primaryErrorConstant] using h
    exact hsame.trans (mul_le_mul_of_nonneg_right (by unfold preRootError; linarith) he)
  | queue =>
    rw [preRoot_cast]
    change |(preRootLaw security .queue queue).weight output - (preRootLaw security .queue queue).weight output| ≤ _
    rw [sub_self, abs_zero]
    exact mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (preRootError_one_le security)) he
  | attachment =>
    rw [preRoot_cast]
    let approximate := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
    let test := fun scalar : LocalReferenceEnergy.Scalar security => ((safeLaw security).map (shiftEquiv security scalar.val)).weight output
    change |approximate.expectation test - (scalarLaw security).expectation test| ≤ _
    have htest (scalar : LocalReferenceEnergy.Scalar security) : |test scalar| ≤ 1 := by
      rw [abs_of_nonneg (((safeLaw security).map (shiftEquiv security scalar.val)).nonneg output)]
      exact ((safeLaw security).map (shiftEquiv security scalar.val)).atom_le_one output
    have hdiff := CyclePatternProgram.expectation_difference_le_l1 approximate (scalarLaw security) test 1 htest
    have hl1 : (∑ scalar, |approximate.weight scalar - (scalarLaw security).weight scalar|) ≤ 1 / (2 : ℝ)^bits :=
      windowApproxLaw_l1 _ _ _ _ (WindowGaussianSampler.squaredWidth_positive security)
        (WindowGaussianSampler.squaredWidth_real security).symm
    apply hdiff.trans
    rw [one_mul]
    exact hl1.trans ((by simpa only [one_mul] using mul_le_mul_of_nonneg_right (preRootError_one_le security) he))

theorem shifted_cast (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : Palette security) :
    (shifted security bits role queue root output.val : ℝ) =
      ((approximatePreRoot security bits role queue).map (shiftEquiv security root)).weight output := by
  rw [shifted, RationalBackgroundProfiles.inverseShift_value, preRoot_cast, FiniteDist.map_equiv_weight]

theorem shifted_bound (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : Palette security) :
    |(shifted security bits role queue root output.val : ℝ)| ≤ 1 := by
  rw [shifted, RationalBackgroundProfiles.inverseShift_value]
  exact preRoot_bound security bits role queue _

theorem shifted_error (security bits : ℕ) (role : BodyRole) (queue : ℤ) (root : CycleRootExpansion.Root security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(shifted security bits role queue root.val output.val : ℝ) - (shiftedLaw security role queue root).weight output| ≤
      preRootError security * (1 / (2 : ℝ)^bits) := by
  rw [shifted, RationalBackgroundProfiles.inverseShift_value, shiftedLaw, FiniteDist.map_equiv_weight]
  exact preRoot_error security bits role queue hprecision hbudget _

theorem meanLaw_convolution (security : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    (meanLaw security role queue).weight output =
      BackgroundCertificates.rootConvolutionProfile security (preRootLaw security role queue).weight output := by
  unfold meanLaw shiftedLaw
  rw [RootIndependentBackground.rootReference_shift_mix, BodyRootAverages.rootAverage_seed]
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  rfl

theorem mean_bound (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    |(mean security bits role queue output.val : ℝ)| ≤ 1 := by
  rw [mean, RationalBackgroundProfiles.convolution_cast]
  exact CalibrationCoordinateError.expectation_abs_bound (RationalProposalProgram.approximateSeedLaw security bits) _ 1
    (fun seed => preRoot_bound security bits role queue _)

theorem mean_error (security bits : ℕ) (role : BodyRole) (queue : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(mean security bits role queue output.val : ℝ) - (meanLaw security role queue).weight output| ≤
      (3 + preRootError security) * (1 / (2 : ℝ)^bits) := by
  rw [meanLaw_convolution]
  exact (RationalBackgroundProfiles.convolution_profile_error security bits (preRoot security bits role queue)
    (preRootLaw security role queue).weight 1 (preRootError security * (1 / (2 : ℝ)^bits))
    (preRoot_bound security bits role queue)
    (preRoot_error security bits role queue hprecision hbudget) output).trans_eq (by ring)

theorem deviation_bound (security bits : ℕ) (role : BodyRole) (queue root : ℤ) (output : Palette security) :
    |(deviation security bits role queue root output.val : ℝ)| ≤ 2 := by
  rw [deviation, Rat.cast_sub]
  exact (abs_sub _ _).trans ((add_le_add (shifted_bound security bits role queue root output)
    (mean_bound security bits role queue output)).trans_eq (by norm_num))

theorem deviation_error (security bits : ℕ) (role : BodyRole) (queue : ℤ) (root : CycleRootExpansion.Root security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(deviation security bits role queue root.val output.val : ℝ) - deviationProfile security role queue root output| ≤
      (2 * preRootError security + 3) * (1 / (2 : ℝ)^bits) := by
  rw [deviation, Rat.cast_sub, deviationProfile, Pi.sub_apply]
  have htriangle :
      |(shifted security bits role queue root.val output.val : ℝ) - (mean security bits role queue output.val : ℝ) -
          ((shiftedLaw security role queue root).weight output - (meanLaw security role queue).weight output)| ≤
        |(shifted security bits role queue root.val output.val : ℝ) - (shiftedLaw security role queue root).weight output| +
          |(mean security bits role queue output.val : ℝ) - (meanLaw security role queue).weight output| := by
    calc
      _ = |((shifted security bits role queue root.val output.val : ℝ) - (shiftedLaw security role queue root).weight output) -
          ((mean security bits role queue output.val : ℝ) - (meanLaw security role queue).weight output)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  exact htriangle.trans ((add_le_add (shifted_error security bits role queue root hprecision hbudget output)
    (mean_error security bits role queue hprecision hbudget output)).trans_eq (by ring))

theorem meanDeviation_bound (security bits : ℕ) (role : BodyRole) (queue : ℤ) (output : Palette security) :
    |(meanDeviation security bits role queue output.val : ℝ)| ≤ 2 := by
  rw [meanDeviation, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    PublicParameterProgram.modulus_value]
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (show 0 < Parameters.modulus security from by
      exact_mod_cast FirstResponse.modulus_pos security)))
  have hu : |(1 : ℝ) / Parameters.modulus security| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq
  exact (abs_sub _ _).trans ((add_le_add (mean_bound security bits role queue output)
    hu).trans_eq (by norm_num))

theorem meanDeviation_error (security bits : ℕ) (role : BodyRole) (queue : ℤ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(meanDeviation security bits role queue output.val : ℝ) - RootMeanPrimary.meanProfile security role queue output| ≤
      (3 + preRootError security) * (1 / (2 : ℝ)^bits) := by
  rw [meanDeviation, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    PublicParameterProgram.modulus_value]
  simpa only [RootMeanPrimary.meanProfile, Pi.sub_apply, LocalReferenceEnergy.uniformReference_weight,
    sub_sub_sub_cancel_right] using
      mean_error security bits role queue hprecision hbudget output

def firstErrorConstant (security : ℕ) : ℝ :=
  2 * RationalMassLiftProgram.errorConstant security +
    RationalTensorInverseProgram.actualBound security * (2 * preRootError security + 3)

def meanErrorConstant (security : ℕ) : ℝ :=
  2 * RationalMassLiftProgram.errorConstant security +
    RationalTensorInverseProgram.actualBound security * (3 + preRootError security)

theorem densityError_nonneg (security : ℕ) :
    0 ≤ firstErrorConstant security ∧ 0 ≤ meanErrorConstant security := by
  have hp := preRootError_one_le security
  have hm := RationalMassLiftProgram.errorConstant_nonneg security
  have ha := RationalTensorInverseProgram.actualBound_nonneg security
  constructor
  · unfold firstErrorConstant; positivity
  · unfold meanErrorConstant; positivity

theorem firstDensity_error (security bits : ℕ) (role : BodyRole) (queue : ℤ) (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(firstDensity security bits role queue root.val output.val : ℝ) -
      RootReferenceColumns.singletonDensityAt security role queue root output| ≤
      firstErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hp := preRootError_one_le security
  have h := RationalMassLiftProgram.current_profile_error security bits
    (deviation security bits role queue root.val) (deviationProfile security role queue root) 2
    ((2 * preRootError security + 3) * (1 / (2 : ℝ)^bits)) (by norm_num) (by positivity)
    (deviation_bound security bits role queue root.val)
    (deviation_error security bits role queue root hprecision hbudget) hfirst hprecision hbudget output
  change |(firstDensity security bits role queue root.val output.val : ℝ) -
    RootReferenceColumns.singletonDensityAt security role queue root output| ≤ _ at h
  exact h.trans_eq (by unfold firstErrorConstant; ring)

theorem meanDensity_error (security bits : ℕ) (role : BodyRole) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(meanDensity security bits role queue output.val : ℝ) -
      RationalMassLiftProgram.actual security (RootMeanPrimary.meanProfile security role queue) output| ≤
      meanErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hp := preRootError_one_le security
  exact (RationalMassLiftProgram.current_profile_error security bits
    (meanDeviation security bits role queue) (RootMeanPrimary.meanProfile security role queue) 2
    ((3 + preRootError security) * (1 / (2 : ℝ)^bits)) (by norm_num) (by positivity)
    (meanDeviation_bound security bits role queue)
    (meanDeviation_error security bits role queue hprecision hbudget) hfirst hprecision hbudget output).trans_eq
      (by unfold meanErrorConstant; ring)

end
end CurrentAFT.RationalRootProfileProgram

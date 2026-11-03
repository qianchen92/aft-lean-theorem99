import CurrentAFT.RationalUnselectedLegNormalized
import CurrentAFT.RationalDiffuseCertificateProgram

/-! # The actual root-shifted centered ordinary control column -/
namespace CurrentAFT.RationalOrdinaryProfileProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def preRoot (security bits source output : ℕ) : ℚ :=
  RationalProposalProgram.center security bits source *
    ((if output = source then 1 else 0) - RationalProposalProgram.center security bits output)

def shifted (security bits source : ℕ) (root : ℤ) (output : ℕ) : ℚ :=
  preRoot security bits source (RationalBackgroundProfiles.inverseShift security root output)

def density (security bits source : ℕ) (root : ℤ) (output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (shifted security bits source root) output

noncomputable section
open scoped Classical
local instance ordinaryFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance ordinarySafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus

def actualPreRoot (security : ℕ) (source : SafePalette security) (output : Palette security) : ℝ :=
  (bodyReference security).weight source * ((if output = source.val then 1 else 0) - (centerLaw security).weight output)

theorem centered_single (security : ℕ) (source center : SafePalette security) :
    centerLinear (bodyReference security) (Pi.single source 1) center =
      (if center.val = source.val then 1 else 0) - (bodyReference security).weight source := by
  simp only [centerLinear, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have heq : center = source ↔ center.val = source.val := Subtype.ext_iff
  simp only [heq]

theorem actualPreRoot_safeMass (security : ℕ) (source : SafePalette security) :
    actualPreRoot security source = BodyChannelEvaluation.safeMass security (centerLinear (bodyReference security) (Pi.single source 1)) := by
  have hcenter : (fun center : SafePalette security =>
      (if center.val = source.val then (1 : ℝ) else 0) - (bodyReference security).weight source) =
      centerLinear (bodyReference security) (Pi.single source 1) := by
    funext center
    exact (centered_single security source center).symm
  rw [← hcenter]
  change actualPreRoot security source = BodyChannelEvaluation.safeMass security
    (fun center : SafePalette security =>
      ((if (center.val : Palette security) = source.val then (1 : ℝ) else 0) - (bodyReference security).weight source))
  rw [BodyChannelEvaluation.safeMass_full security
    (fun color : Palette security => (if color = source.val then 1 else 0) - (bodyReference security).weight source)]
  funext output
  unfold actualPreRoot
  by_cases h : output = source.val
  · subst output
    simp only [if_true]
    rfl
  · simp only [if_neg h]
    ring

theorem shifted_actual (security : ℕ) (source : SafePalette security) (root : Root security) (output : Palette security) :
    actualPreRoot security source ((shiftEquiv security root.val).symm output) =
      RootMassColumns.ordinaryMassAt security root (centerLinear (bodyReference security) (Pi.single source 1)) output := by
  rw [actualPreRoot_safeMass]
  exact (SelectedOrdinaryMean.push_root security root _ output).symm

theorem preRoot_bound (security bits : ℕ) (source output : Palette security) :
    |(preRoot security bits source.val output.val : ℝ)| ≤ 1 := by
  let hsource := RationalProposalProgram.approximateCenterLaw security bits
  have ha : 0 ≤ (RationalProposalProgram.center security bits source.val : ℝ) := hsource.nonneg source
  have hb : 0 ≤ (RationalProposalProgram.center security bits output.val : ℝ) := hsource.nonneg output
  have hu : (RationalProposalProgram.center security bits output.val : ℝ) ≤ 1 := hsource.atom_le_one output
  rw [preRoot, Rat.cast_mul, Rat.cast_sub, abs_mul]
  have hdelta : |(((if output.val = source.val then 1 else 0) : ℚ) : ℝ) -
      (RationalProposalProgram.center security bits output.val : ℝ)| ≤ 1 := by
    split_ifs <;> norm_num only [Rat.cast_one, Rat.cast_zero] <;> rw [abs_le] <;> constructor <;> linarith
  simpa only [mul_one] using mul_le_mul (RationalDiffuseCertificateProgram.center_bound security bits source) hdelta
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

def profileErrorConstant (security : ℕ) : ℝ := 2 * RationalBackgroundDensities.centerErrorConstant security

theorem preRoot_error (security bits : ℕ) (source : SafePalette security) (output : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(preRoot security bits source.val.val output.val : ℝ) - actualPreRoot security source output| ≤
      profileErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let A := RationalBackgroundDensities.centerErrorConstant security
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  have hA : 0 ≤ A := by unfold A RationalBackgroundDensities.centerErrorConstant; positivity
  have he : 0 ≤ epsilon := by positivity
  have hsource : |(RationalProposalProgram.center security bits source.val.val : ℝ) - (bodyReference security).weight source| ≤ A * epsilon := by
    simpa only [A, epsilon, bodyReference, supportedLaw, centerLaw, RationalBackgroundDensities.centerErrorConstant] using
      RationalProposalProgram.center_error security bits source.val hprecision hbudget
  have houtput : |(RationalProposalProgram.center security bits output.val : ℝ) - (centerLaw security).weight output| ≤ A * epsilon := by
    simpa only [A, epsilon, centerLaw, RationalBackgroundDensities.centerErrorConstant] using
      RationalProposalProgram.center_error security bits output hprecision hbudget
  have hdelta : |((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) -
      (RationalProposalProgram.center security bits output.val : ℝ)| ≤ 1 := by
    have hb := (RationalProposalProgram.approximateCenterLaw security bits).nonneg output
    have hu := (RationalProposalProgram.approximateCenterLaw security bits).atom_le_one output
    change 0 ≤ (RationalProposalProgram.center security bits output.val : ℝ) at hb
    change (RationalProposalProgram.center security bits output.val : ℝ) ≤ 1 at hu
    split_ifs <;> norm_num only [Rat.cast_one, Rat.cast_zero] <;> rw [abs_le] <;> constructor <;> linarith
  have ha : |(bodyReference security).weight source| ≤ 1 := by
    rw [abs_of_nonneg ((bodyReference security).nonneg source)]
    exact (bodyReference security).atom_le_one source
  rw [preRoot, Rat.cast_mul, Rat.cast_sub]
  have hsame : (((if output.val = source.val.val then (1 : ℚ) else 0) : ℚ) : ℝ) = (if output = source.val then 1 else 0 : ℝ) := by
    by_cases h : output = source.val
    · subst output; simp
    · have hv : output.val ≠ source.val.val := fun heq => h (Fin.ext heq)
      simp [h, hv]
  unfold actualPreRoot
  rw [← hsame]
  have hsplit : (RationalProposalProgram.center security bits source.val.val : ℝ) *
      (((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) - (RationalProposalProgram.center security bits output.val : ℝ)) -
      (bodyReference security).weight source * (((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) - (centerLaw security).weight output) =
      ((RationalProposalProgram.center security bits source.val.val : ℝ) - (bodyReference security).weight source) *
        (((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) - (RationalProposalProgram.center security bits output.val : ℝ)) +
      (bodyReference security).weight source * ((centerLaw security).weight output - (RationalProposalProgram.center security bits output.val : ℝ)) := by ring
  rw [hsplit]
  have hfirst : |((RationalProposalProgram.center security bits source.val.val : ℝ) - (bodyReference security).weight source) *
      (((if output.val = source.val.val then 1 else 0 : ℚ) : ℝ) - (RationalProposalProgram.center security bits output.val : ℝ))| ≤
      (A * epsilon) * 1 := by
    rw [abs_mul]
    exact mul_le_mul hsource hdelta (abs_nonneg _) (by positivity)
  have hsecond : |(bodyReference security).weight source *
      ((centerLaw security).weight output - (RationalProposalProgram.center security bits output.val : ℝ))| ≤ 1 * (A * epsilon) := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul ha houtput (abs_nonneg _) (by norm_num)
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq
    (by unfold profileErrorConstant; dsimp only [A, epsilon]; ring))

def errorConstant (security : ℕ) : ℝ := RationalMassLiftProgram.errorConstant security +
  RationalTensorInverseProgram.actualBound security * profileErrorConstant security

theorem density_error (security bits : ℕ) (source : SafePalette security) (root : Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Palette security) :
    |(density security bits source.val.val root.val output.val : ℝ) -
      RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1) output| ≤
      errorConstant security * (1 / (2 : ℝ)^bits) := by
  have hbound (color : Palette security) : |(shifted security bits source.val.val root.val color.val : ℝ)| ≤ 1 := by
    rw [shifted, RationalBackgroundProfiles.inverseShift_value]
    exact preRoot_bound security bits source.val _
  have hdiff (color : Palette security) : |(shifted security bits source.val.val root.val color.val : ℝ) -
      RootMassColumns.ordinaryMassAt security root (centerLinear (bodyReference security) (Pi.single source 1)) color| ≤
      profileErrorConstant security * (1 / (2 : ℝ)^bits) := by
    rw [shifted, RationalBackgroundProfiles.inverseShift_value, ← shifted_actual]
    exact preRoot_error security bits source _ hprecision hbudget
  have h := RationalMassLiftProgram.current_profile_error security bits (shifted security bits source.val.val root.val) _
    1 (profileErrorConstant security * (1 / (2 : ℝ)^bits)) (by norm_num)
    (by unfold profileErrorConstant RationalBackgroundDensities.centerErrorConstant; positivity)
    hbound hdiff hfirst hprecision hbudget output
  exact h.trans_eq (by unfold errorConstant; ring)

end
end CurrentAFT.RationalOrdinaryProfileProgram

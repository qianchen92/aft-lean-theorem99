import CurrentAFT.RootLegCoefficientBounds

/-! Pure-primary positive denominators for the actual singleton root means. -/

namespace CurrentAFT.RootMeanPrimary

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  UniformBodyProfiles CycleRootExpansion RootTaggedLocal PrimaryTensorInverse PrimaryMassFamilies
  ControlCoordinates GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  BackgroundFamilies BackgroundRates BackgroundEvaluation BackgroundFirstEvaluation
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def meanProfile (security : ℕ) (role : BodyRole) (queue : ℤ) : ActualControls.Palette security → ℝ :=
  (meanLaw security role queue).weight - (uniformReference security).weight

theorem meanProfile_mass (security : ℕ) (role : BodyRole) (queue : ℤ) :
    (∑ color, meanProfile security role queue color) = 0 := by
  simp only [meanProfile, Pi.sub_apply, Finset.sum_sub_distrib, FiniteDist.sum_one, sub_self]

theorem meanProfile_energy (security : ℕ) (role : BodyRole) (queue : ℤ) :
    profileSquareNorm (primaryLaw security).weight (meanProfile security role queue) ≤ 2 * deviation security ^ 2 := by
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (meanLaw_uniform_norm security role queue) 2
  change ‖ProfileHilbert.whiten (uniformReference security).weight (meanProfile security role queue)‖ ^ 2 ≤ _ at hnorm
  rw [ProfileHilbert.whiten_norm_sq _ _ (uniformReference security).nonneg] at hnorm
  exact (uniform_to_primary_energy security _).trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))

def positiveAtom (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) : ActualFamily security order :=
  massCertificateFamily security order 1 horder (oneWordProfile (meanProfile security role queue))
    (oneWordProfile_centered _ (meanProfile_mass security role queue)) (oneWordProfile_symmetric _)

theorem positiveAtom_zero (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    positiveAtom security order horder role queue (zeroArity order) = 0 := by
  unfold positiveAtom massCertificateFamily
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
  change 0 = 1 at h
  omega

theorem positiveAtom_norm (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (positiveAtom security order horder role queue) ≤ 2064 / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hd := deviation_nonneg security
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have henergy : massEnergy security 1 (oneWordProfile (meanProfile security role queue)) ≤ 2 * deviation security ^ 2 := by
    rw [show massEnergy security 1 (oneWordProfile (meanProfile security role queue)) =
      profileSquareNorm (primaryLaw security).weight (meanProfile security role queue) from
        oneWordProfile_energy _ _]
    exact meanProfile_energy security role queue
  have hsqrt : Real.sqrt (massEnergy security 1 (oneWordProfile (meanProfile security role queue))) ≤ 2 * deviation security := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    exact henergy.trans (by nlinarith [sq_nonneg (deviation security)])
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1 <;> ring
  have h := massCertificateFamily_norm security order 1 horder (primaryFactor security) (bodyFactor security) hp
    (oneWordProfile (meanProfile security role queue))
    (oneWordProfile_centered _ (meanProfile_mass security role queue)) (oneWordProfile_symmetric _)
  simp only [pow_one] at h
  apply h.trans
  calc
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (8 * (Parameters.base security : ℝ)) * (2 * deviation security) :=
      mul_le_mul (mul_le_mul (le_of_eq (primaryFactor_eq security)) hinv (by positivity) (by positivity))
        hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by unfold deviation; field_simp; norm_num

def positiveFamily (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) : ActualFamily security order :=
  1 + positiveAtom security order horder role queue

def positiveInverse (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) : ActualFamily security order :=
  backgroundInverse (primaryLaw security) (bodyReference security) order (positiveFamily security order horder role queue)

theorem positiveFamily_unit_constant (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    positiveFamily security order horder role queue (zeroArity order) = (1 : ActualFamily security order) (zeroArity order) := by
  change (1 : ActualFamily security order) (zeroArity order) + positiveAtom security order horder role queue (zeroArity order) = _
  rw [positiveAtom_zero, add_zero]

theorem positiveFamily_image (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    evaluation security order (positiveFamily security order horder role queue) =
      TruncatedOutput.quotientMap order (singleGenerating (uniformReference security).weight (meanLaw security role queue).weight) := by
  unfold positiveFamily positiveAtom
  rw [map_add, map_one, massCertificateFamily_image, massPolynomial_one,
    singleGenerating_mass_one _ _ (meanLaw security role queue).sum_one, map_add, map_one]
  rfl

theorem positiveInverse_mul (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    positiveInverse security order horder role queue * positiveFamily security order horder role queue = 1 :=
  backgroundInverse_mul _ _ _ _ (positiveFamily_unit_constant security order horder role queue)

theorem positiveInverse_norm (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (positiveInverse security order horder role queue) ≤ 2 := by
  have hb := FirstResponse.base_pos security
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have htwo : (2 : ℝ) ≤ (Parameters.base security : ℝ) := by exact_mod_cast Parameters.base_ge_two security
  have hpower : (4128 : ℝ) ≤ (Parameters.base security : ℝ) ^ 94 := by
    exact (by norm_num : (4128 : ℝ) ≤ 2 ^ 94).trans (pow_le_pow_left₀ (by norm_num) htwo 94)
  have hhalf : 2064 / (Parameters.base security : ℝ) ^ 94 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hb _)).mpr
    linarith
  have hdefect : familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (1 - positiveFamily security order horder role queue) ≤ (1 / 2 : ℝ) := by
    have heq : 1 - positiveFamily security order horder role queue = - positiveAtom security order horder role queue := by
      unfold positiveFamily
      abel
    rw [heq, familyNorm_neg]
    exact (positiveAtom_norm security order horder role queue).trans hhalf
  exact (backgroundInverse_norm_le _ _ _ _ _ hp hbdy _ (1 / 2) (by norm_num) hdefect).trans_eq (by norm_num)

end
end CurrentAFT.RootMeanPrimary

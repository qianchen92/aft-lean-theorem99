import CurrentAFT.RootLegNormalized

/-! Pure-primary finite reciprocal for the complete actual unselected leg. -/

namespace CurrentAFT.RootLegReciprocal

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock RootIndependentBackground RootBackgroundPolynomial
  CycleRootExpansion RootTaggedLegHigher RootLegCoefficientFamily RootLegCoefficientNorm
  RootLegCoefficientLinear RootLegCoefficientBounds RootLegNormalized PrimaryOnlyFamily
  ControlCoordinates GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  BackgroundFamilies BackgroundRates BackgroundEvaluation
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def meanPositiveLaw (security : ℕ) : FiniteDist (Fin 3 → ActualControls.Palette security) :=
  (rootReference security).mix (fun root => primaryLawAt security root.val)

theorem meanPositiveLaw_weight (security : ℕ) :
    (meanPositiveLaw security).weight = rawMassLinear security (fun _ => 1) := by
  funext word
  simp only [meanPositiveLaw, FiniteDist.mix_weight, rawMassLinear,
    LinearMap.coe_mk, AddHom.coe_mk, mul_one]

theorem meanPositiveLaw_energy (security : ℕ) :
    primaryMassEnergy security (meanPositiveLaw security).weight ≤ 32 * pairBudget security := by
  rw [meanPositiveLaw_weight]
  apply (primaryMassEnergy_uniform_le security _).trans
  have h := rawMass_uniform_energy security (fun _ => 1)
  simp only [FiniteDist.l2Sq, one_pow, FiniteDist.expectation_const, mul_one] at h
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 8)).trans_eq (by ring)

theorem meanPositiveLaw_generating (security : ℕ) :
    blockGenerating security (meanPositiveLaw security) = LegPolynomialEvaluation.legGenerating security := by
  rw [meanPositiveLaw, blockGenerating_mix]
  exact primary_root_average security

def positive (security order : ℕ) : ActualFamily security order :=
  RootLegNormalized.positiveFamily security order (meanPositiveLaw security)

def reciprocal (security order : ℕ) : ActualFamily security order :=
  backgroundInverse (primaryLaw security) (bodyReference security) order (positive security order)

theorem positive_unit_constant (security order : ℕ) :
    positive security order (zeroArity order) = (1 : ActualFamily security order) (zeroArity order) :=
  RootLegNormalized.positiveFamily_zeroArity security order _

theorem reciprocal_mul (security order : ℕ) : reciprocal security order * positive security order = 1 :=
  backgroundInverse_mul _ _ _ _ (positive_unit_constant security order)

theorem selected_primaryOnly (security order : ℕ) (mass : (Fin 3 → ActualControls.Palette security) → ℝ) (selected : Finset (Fin 3)) :
    PrimaryOnly (primaryLaw security) (bodyReference security) order (selectedFamily security order mass selected) := by
  unfold selectedFamily
  split_ifs
  · exact primaryOnly_single _ _ _ _ rfl _
  · exact primaryOnly_zero _ _ _

theorem complete_primaryOnly (security order : ℕ) (mass : (Fin 3 → ActualControls.Palette security) → ℝ) :
    PrimaryOnly (primaryLaw security) (bodyReference security) order (RootLegNormalized.completeFamily security order mass) := by
  unfold RootLegNormalized.completeFamily
  apply primaryOnly_add
  · exact primaryOnly_smul _ _ _ _ _ (primaryOnly_one _ _ _)
  · apply primaryOnly_sum
    intro selected _
    exact selected_primaryOnly security order mass selected

theorem positive_primaryOnly (security order : ℕ) : PrimaryOnly (primaryLaw security) (bodyReference security) order (positive security order) :=
  complete_primaryOnly security order _

theorem reciprocal_primaryOnly (security order : ℕ) : PrimaryOnly (primaryLaw security) (bodyReference security) order (reciprocal security order) :=
  primaryOnly_inverse _ _ _ _ (positive_primaryOnly security order)

theorem positive_image (security order : ℕ) :
    evaluation security order (positive security order) =
      TruncatedOutput.quotientMap order (LegPolynomialEvaluation.legGenerating security) := by
  have h := RootLegNormalized.completeFamily_image security order (meanPositiveLaw security).weight
    (bodyForm security) (bodyForm_homogeneous security)
  have hpoly : centeredGeneratingLinear (uniformReference security).weight (meanPositiveLaw security).weight =
      blockGenerating security (meanPositiveLaw security) := by
    have huniform : (uniformReference security).weight = FringeCertificate.uniformProfile security := by
      funext color
      rw [uniformReference_weight]
      simp only [FringeCertificate.uniformProfile, one_div]
    simp only [centeredGeneratingLinear, blockGenerating, BackgroundPolynomialEvaluation.finiteGenerating,
      LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def, MvPolynomial.algebraMap_eq]
    rw [huniform]
  rw [hpoly, meanPositiveLaw_generating] at h
  exact h

theorem reciprocal_physical (security order : ℕ) :
    evaluation security order (reciprocal security order) *
      TruncatedOutput.quotientMap order (LegPolynomialEvaluation.legGenerating security) = 1 := by
  rw [← positive_image, ← map_mul, reciprocal_mul, map_one]

def positiveCost (security : ℕ) : ℝ := 8 * normalizedFactor security * Real.sqrt (32 * pairBudget security)

theorem positive_defect_norm (security order : ℕ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (positive security order - 1) ≤ positiveCost security := by
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have hequal : positive security order - 1 = ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
      selectedFamily security order (meanPositiveLaw security).weight selected := by
    unfold positive RootLegNormalized.positiveFamily RootLegNormalized.completeFamily
    rw [(meanPositiveLaw security).sum_one, one_smul]
    abel
  rw [hequal]
  apply (familyNorm_sum_le _ _ _ _ _ hp hb _ _).trans
  have hpoint (selected : Finset (Fin 3)) (hselected : selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅) :
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (selectedFamily security order (meanPositiveLaw security).weight selected) ≤
          normalizedFactor security * Real.sqrt (32 * pairBudget security) := by
    have h := selectedFamily_norm security order (meanPositiveLaw security).weight selected
      (primaryFactor security) (bodyFactor security) hp
    have henergy := Real.sqrt_le_sqrt (meanPositiveLaw_energy security)
    have hpower : normalizedFactor security ^ selected.card ≤ normalizedFactor security := by
      have hnonempty := Finset.mem_erase.mp hselected |>.1
      have hcard : 1 ≤ selected.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hnonempty)
      simpa only [pow_one] using pow_le_pow_of_le_one (normalizedFactor_nonneg security) (normalizedFactor_le_one security) hcard
    apply h.trans
    calc
      _ = normalizedFactor security ^ selected.card * Real.sqrt (primaryMassEnergy security (meanPositiveLaw security).weight) := by
        unfold normalizedFactor
        rw [show (8 : ℝ) = 2 * 4 by norm_num]
        simp only [mul_pow, div_pow]
        ring
      _ ≤ _ := mul_le_mul hpower henergy (Real.sqrt_nonneg _) (normalizedFactor_nonneg security)
  apply (Finset.sum_le_sum hpoint).trans
  have hcard : (((Finset.univ : Finset (Finset (Fin 3))).erase ∅).card : ℝ) ≤ 8 := by
    exact_mod_cast (show ((Finset.univ : Finset (Finset (Fin 3))).erase ∅).card ≤ 8 by simp)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right hcard (mul_nonneg (normalizedFactor_nonneg security) (Real.sqrt_nonneg _))).trans_eq (by unfold positiveCost; ring)

def positiveConstant : ℝ := 1536 * Real.sqrt LocalRaisingBounds.pairConstant

theorem positiveCost_decay (security : ℕ) : positiveCost security ≤ positiveConstant / (Parameters.base security : ℝ) ^ 39 := by
  have hb := FirstResponse.base_pos security
  unfold positiveCost
  calc
    _ ≤ 8 * (32 / (Parameters.base security : ℝ) ^ 63) *
        (6 * Real.sqrt LocalRaisingBounds.pairConstant * (Parameters.base security : ℝ) ^ 24) := by
      gcongr
      · exact normalizedFactor_decay security
      · exact sqrtBudget_polynomial security
    _ = _ := by unfold positiveConstant; field_simp; ring

theorem reciprocal_norm_eventually (order : ℕ) :
    ∀ᶠ security : ℕ in atTop,
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (reciprocal security order) ≤ 2 := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * positiveConstant)
  filter_upwards [eventually_ge_atTop threshold] with security hsecurity
  have hb := FirstResponse.base_pos security
  have hbase : 2 * positiveConstant ≤ (Parameters.base security : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 39 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 39 by omega)
  have hhalf : positiveConstant / (Parameters.base security : ℝ) ^ 39 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hb _)).mpr
    linarith
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have hdefect : familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (1 - positive security order) ≤ (1 / 2 : ℝ) := by
    rw [show 1 - positive security order = -(positive security order - 1) by abel, familyNorm_neg]
    exact (positive_defect_norm security order).trans ((positiveCost_decay security).trans hhalf)
  exact (backgroundInverse_norm_le _ _ _ _ _ hp hbdy _ (1 / 2) (by norm_num) hdefect).trans_eq (by norm_num)

end
end CurrentAFT.RootLegReciprocal
